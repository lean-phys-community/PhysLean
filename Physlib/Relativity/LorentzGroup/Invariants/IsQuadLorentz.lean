/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
public import Physlib.Relativity.LightConeDeriv
public import Physlib.Relativity.SL2C.AxisRotations
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Data.Matrix.Reflection
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants among four four-vector indices

`IsQuadLorentz repLorentz T` says that a family `T`, indexed by four four-vector
indices and valued in a module `B` carrying a representation of `SL(2,ℂ)`, transforms
as a tensor `T^{μ₁ μ₂ μ₃ μ₄}`.

The main theorem `exists_smul_contraction_of_invariant` classifies the Lorentz
invariants in the span of the components: every invariant element is a linear
combination of the outer, inner and split metric contractions and the Levi-Civita
contraction. The four contractions are themselves Lorentz invariant
(`repLorentz_outerContraction` and its three companions): the metric ones because
`Λ η Λᵀ = η` is what defines the Lorentz group, the Levi-Civita one because the
transformations coming from `SL(2,ℂ)` are proper. That is what makes the error term of
the classification modulo a Lorentz-stable submodule invariant as well
(`exists_smul_contraction_of_invariant_subset`), the error being the difference of two
invariants, and it is what turns both classifications into the equivalences
`mem_span_and_invariant_iff` and `mem_span_sup_invariant_iff`.

The section headings tell the story: the light-cone bases (B) grade the span by boost
weight, the weight-zero projection of a generator gives the recursion rounds (C), a
sieve along the three axes (D) cuts an invariant down to the tied pieces supported on
paired-or-distinct indices (E), rotation averaging reduces to `22` orbit sums (F) on
which the boost average is an explicit integer matrix (G), and a polynomial certificate
collapses the iterated rounds to the projector onto the four contractions (H, I, J).
The two symbols the contractions are built from are shown invariant in I.5 and the
contractions themselves in I.6.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups Lorentz SL2C

/-!

## A. Quadruple Lorentz tensors and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by four four-vector indices, transforms as
  a tensor `T^{μ₁ μ₂ μ₃ μ₄}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsQuadLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 4 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 4), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsQuadLorentz
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsQuadLorentz B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsQuadLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 4 → (Fin 1 ⊕ Fin 3)) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 4 → (Fin 1 ⊕ Fin 3)) → ℂ, y = ∑ d, c d • T d)
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

## B. The light-cone basis along one axis

## B.1. Light-cone components: their span and boost weight

Along a spatial axis `i` the coordinate components recombine into the light-cone
components `lightCone i c`, which span the same space and are homogeneous of boost
weight `∑ j, lightConeWeight (c j)`.

-/

open BoostWeight

/-- The axis-`i` light-cone component of `T` at the light-cone multi-index `c`. -/
noncomputable def lightCone  (hT : IsQuadLorentz B repLorentz T) (i : Fin 3) (c : Fin 4 → Fin 4) :  B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the coordinate components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 4 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

lemma eq_sum_lightCone (i : Fin 3) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 4 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 4 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

lemma span_eq_lightCone (hT : IsQuadLorentz B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ c, ℂ ∙ hT.lightCone i c := by
  rw [span]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun c => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_lightCone i d]
    exact sum_mem fun c _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.lightCone_mem_span i c


lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ x : Fin 4 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x)
        = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ x : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        exact sum_prod_lightConeCoeff i c a ht
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-!

## B.2. Integer and rational mirrors of the light-cone coefficients

Mirrors of the light-cone coefficients over `ℤ` and `ℚ`, so that the vanishing of
coefficients can be settled by `decide`.

-/

/-- Integer mirror of `lightConeCoeff`. -/
def lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 0 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then -1 else 0)
  else if κ = 1 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then 1 else 0)
  else if κ = 2 then (if μ = Sum.inr (i + 1) then 1 else 0)
  else (if μ = Sum.inr (i + 2) then 1 else 0)

/-- The integer mirror casts to the light-cone coefficients. -/
lemma coe_lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) :
    ((lightConeCoeffZ i κ μ : ℤ) : ℂ) = lightConeCoeff i κ μ := by
  rw [lightConeCoeffZ, lightConeCoeff]
  split_ifs <;> norm_num

/-- Rational mirror of `lightConeCoeffInv`: entries `0`, `±2⁻¹`
  and `1`, so ℚ-valued (like `lightConeTransition`) rather than integer. -/
def lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℚ :=
  if μ = Sum.inl 0 then (if κ = 0 then 2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr i then (if κ = 0 then -2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 1 else 0)
  else (if κ = 3 then 1 else 0)

/-- The rational mirror casts to the inverse light-cone coefficients. -/
lemma coe_lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvQ i μ κ : ℚ) : ℂ) = lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvQ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- Where the integer mirror vanishes, the inverse coefficient vanishes too: the zero
  pattern of `lightConeCoeffInv` is the transpose of that of `lightConeCoeffZ`. -/
lemma lightConeCoeffInv_eq_zero_of_coeffZ_eq_zero (i : Fin 3) (κ : Fin 4)
    (μ : Fin 1 ⊕ Fin 3) (h : lightConeCoeffZ i κ μ = 0) : lightConeCoeffInv i μ κ = 0 := by
  rcases μ with a | j
  · rw [Subsingleton.elim a 0] at h ⊢
    fin_cases i <;> fin_cases κ <;> simp_all [lightConeCoeffZ, lightConeCoeffInv]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp_all [lightConeCoeffZ, lightConeCoeffInv]

/-!

## Aside: Vanishing of homogeneous boost-weight sums

Pure weight-grading statements with no `T` involved: the weight spaces are independent,
so a finite homogeneous sum vanishes only if every term does, and a weight-zero element
of such a sum is its weight-zero term. These belong next to
`boostWeightSubmodule_iSupIndep` in `WeightGrading`.

-/

/-- Components of a vanishing homogeneous sum vanish: the boost-weight spaces are
  independent. -/
lemma eq_zero_of_sum_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A}
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (hsum : ∑ m ∈ s, w m = 0) :
    ∀ m ∈ s, w m = 0 := by
  intro m₀ hm₀
  refine Submodule.disjoint_def.1
    (iSupIndep_def.1 (boostWeightSubmodule_iSupIndep rep) m₀) (w m₀) (hw m₀ hm₀) ?_
  have h : w m₀ = -∑ m ∈ s.erase m₀, w m :=
    eq_neg_of_add_eq_zero_left (by rw [Finset.add_sum_erase s w hm₀]; exact hsum)
  rw [h]
  exact neg_mem (sum_mem fun m hm => Submodule.mem_iSup_of_mem m
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hm)
      (hw m (Finset.mem_of_mem_erase hm))))

/-- A weight-zero element of a homogeneous sum is its weight-zero component: all the
  other components must vanish. -/
lemma eq_component_zero_of_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A} {x : A}
    (hx : x ∈ boostWeightSubmodule rep i 0)
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (h0 : (0 : ℤ) ∈ s) (hsum : x = ∑ m ∈ s, w m) :
    x = w 0 := by
  have hv : ∀ m ∈ s, Function.update w 0 (w 0 - x) m ∈ boostWeightSubmodule rep i m := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [Function.update_self]
      exact sub_mem (hw 0 h0) hx
    · rw [Function.update_of_ne h]
      exact hw m hm
  have hsum0 : ∑ m ∈ s, Function.update w 0 (w 0 - x) m = 0 := by
    rw [Finset.sum_update_of_mem h0, hsum, ← Finset.add_sum_erase s w h0, Finset.erase_eq]
    abel
  have h := eq_zero_of_sum_mem_boostWeightSubmodule hv hsum0 0 h0
  rw [Function.update_self] at h
  exact (sub_eq_zero.1 h).symm

/-!

## C. The weight-zero projection of a generator

## C.1. The boost-weight components of a generator

Each generator `T e` is the sum of its boost-weight components `monoComponent i e m`
over the weight support along any axis.

-/

/-- The axis-`i` weight-`m` component of the generator `T e`: the weight-`m` partial
  sum of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) (m : ℤ) :
    hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The possible axis-`i` boost weights of a component: the total light-cone weights
  of the axis-`i` light-cone monomials appearing in `eq_sum_lightCone` with a nonzero
  coefficient — those reachable through slots where the integer mirror `lightConeCoeffZ`
  does not vanish. Computable, so membership can be settled by `decide`. -/
def boostSupport (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) : Finset ℤ :=
  (Finset.univ.filter fun c : Fin 4 → Fin 4 =>
      ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0).image
    fun c => ∑ s, lightConeWeight (c s)

lemma eq_sum_monoComponent (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ boostSupport i e, hT.monoComponent i e m := by
  have hne : ∀ c : Fin 4 → Fin 4,
      ((∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c ≠ 0) →
      ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0 := fun c hc s hs =>
    absurd (by rw [Finset.prod_eq_zero (Finset.mem_univ s)
      (lightConeCoeffInv_eq_zero_of_coeffZ_eq_zero i (c s) (e s) hs), zero_smul]) hc
  calc T e
      = ∑ c : Fin 4 → Fin 4,
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        hT.eq_sum_lightCone i e
    _ = ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
            ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0),
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        (Finset.sum_filter_of_ne (fun c _ => hne c)).symm
    _ = ∑ m ∈ boostSupport i e,
          ∑ c ∈ (Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
              ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0)).filter
            (fun c => (∑ s, lightConeWeight (c s)) = m),
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        (Finset.sum_fiberwise_of_maps_to
          (fun c hc => Finset.mem_image_of_mem _ hc) _).symm
    _ = ∑ m ∈ boostSupport i e, hT.monoComponent i e m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.filter_comm, monoComponent]
        exact Finset.sum_filter_of_ne fun c _ => hne c

/-- The total light-cone weight of four slots is even and lies between `-8` and `8`. -/
lemma sum_lightConeWeight_mem (c : Fin 4 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ) := by
  have hweight (κ : Fin 4) :
      ∃ q : ℤ, -1 ≤ q ∧ q ≤ 1 ∧ lightConeWeight κ = 2 * q := by
    fin_cases κ
    · exact ⟨1, by norm_num [lightConeWeight]⟩
    · exact ⟨-1, by norm_num [lightConeWeight]⟩
    · exact ⟨0, by norm_num [lightConeWeight]⟩
    · exact ⟨0, by norm_num [lightConeWeight]⟩
  obtain ⟨q0, hq0_lower, hq0_upper, hq0⟩ := hweight (c 0)
  obtain ⟨q1, hq1_lower, hq1_upper, hq1⟩ := hweight (c 1)
  obtain ⟨q2, hq2_lower, hq2_upper, hq2⟩ := hweight (c 2)
  obtain ⟨q3, hq3_lower, hq3_upper, hq3⟩ := hweight (c 3)
  rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

set_option maxRecDepth 10000 in
/-- A component is the sum of its weight components over the full weight set: as
  `eq_sum_monoComponent` but over the fixed weight set common to all components. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

/-!

## C.2. The weight-zero transition matrix

The matrix of the axis-`i` weight-zero projection in the `T`-basis: a sum over balanced
sector patterns of per-slot sector matrices.

-/

/-- The three light-cone sectors of one index: `0` the raising direction `κ = 0`,
  `1` the lowering direction `κ = 1`, `2` the transverse plane `κ ∈ {2, 3}`. -/
def sectorIndex : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The boost weight of each sector. -/
def sectorWeight : Fin 3 → ℤ := ![2, -2, 0]

/-- The light-cone weight of an index is the weight of its sector. -/
lemma lightConeWeight_eq_sectorWeight (κ : Fin 4) :
    lightConeWeight κ = sectorWeight (sectorIndex κ) := by decide +revert

/-- The per-slot sector transition matrix: the single-index composite
  `lightConeCoeffInvQ · lightConeCoeffZ` summed over the light-cone directions of one
  sector. The three sectors resolve the identity, and `weightZeroTransition` is by
  definition the balanced-sector convolution of these small matrices. -/
def slotTransition (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
    lightConeCoeffInvQ i μ κ' * (lightConeCoeffZ i κ' ν : ℚ)

/-- The matrix of the axis-`i` weight-zero projection in the `T`-basis: the
  coefficient of `T d` in the re-expansion of `monoComponent i e 0` through the
  light-cone basis, as the sum over balanced sector patterns — as many raising as
  lowering slots, `19` patterns — of the product of the per-slot sector matrices.
  Rational-valued and computable; `weightZeroTransition_eq_sum_lightCone` gives the
  equivalent sum over the `70` weight-zero light-cone monomials. -/
def weightZeroTransition (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ w ∈ Finset.univ.filter (fun w : Fin 4 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
    ∏ s, slotTransition i (w s) (e s) (d s)

/-- Weight-zero light-cone sums are balanced-sector convolutions: a sum over the
  weight-zero light-cone monomials of a product of slot factors regroups as the sum
  over balanced sector patterns of the product of the slotwise sector sums. -/
lemma sum_weightZero_eq_sum_sector {R : Type*} [CommSemiring R] (f : Fin 4 → Fin 4 → R) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, f s (c s)
      = ∑ w ∈ Finset.univ.filter (fun w : Fin 4 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
          ∏ s, ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = w s), f s κ' := by
  have hmaps : ∀ c ∈ Finset.univ.filter
      (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
      (fun s => sectorIndex (c s)) ∈ Finset.univ.filter
        (fun w : Fin 4 → Fin 3 => (∑ s, sectorWeight (w s)) = 0) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc]
    exact (Finset.sum_congr rfl fun s _ => lightConeWeight_eq_sectorWeight (c s)).symm
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw0 : (∑ s, sectorWeight (w s)) = 0 := (Finset.mem_filter.1 hw).2
  have hfiber : (Finset.univ.filter
        (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0)).filter
      (fun c => (fun s => sectorIndex (c s)) = w)
      = Fintype.piFinset
          (fun s => Finset.univ.filter (fun κ : Fin 4 => sectorIndex κ = w s)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      funext_iff]
    constructor
    · rintro ⟨-, hcw⟩ s
      exact hcw s
    · intro hcw
      refine ⟨?_, hcw⟩
      rw [show (∑ s, lightConeWeight (c s)) = ∑ s, sectorWeight (w s) from
        Finset.sum_congr rfl fun s _ => by rw [lightConeWeight_eq_sectorWeight, hcw s]]
      exact hw0
  rw [hfiber]
  exact (Finset.prod_univ_sum
    (fun s => Finset.univ.filter fun κ' : Fin 4 => sectorIndex κ' = w s)
    (fun s κ' => f s κ')).symm

/-- The weight-zero transition as a light-cone sum: the sector convolution defining
  `weightZeroTransition` expands to the sum over weight-zero light-cone monomials of
  the composite `lightConeCoeffInvQ · lightConeCoeffZ` slot coefficients. -/
lemma weightZeroTransition_eq_sum_lightCone (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition i d e
      = ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ) := by
  rw [weightZeroTransition]
  exact (sum_weightZero_eq_sum_sector
    (fun s κ => lightConeCoeffInvQ i (e s) κ * (lightConeCoeffZ i κ (d s) : ℚ))).symm

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i e 0`
  is the `e`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    hT.monoComponent i e 0
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((weightZeroTransition i d e : ℚ) : ℂ) • T d := by
  rw [monoComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [weightZeroTransition_eq_sum_lightCone]
  push_cast
  simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ, Finset.prod_mul_distrib]

/-!

## C.3. The boost average and iterated rounds

An element of weight zero along all three axes re-expands through any power of the
boost-average matrix applied to its coefficients.

-/

/-- The boost-average matrix `M`: the matrix of `3⁻¹(π₀⁰ + π₁⁰ + π₂⁰)` in the
  `T`-basis — the average over the three axes of the weight-zero transition matrices.
  Its powers drive the endgame recursion, and the certificate is a fixed rational
  combination of them. -/
def boostAverageTransition :
    Matrix (Fin 4 → Fin 1 ⊕ Fin 3) (Fin 4 → Fin 1 ⊕ Fin 3) ℚ :=
  Matrix.of fun d e => (3⁻¹ : ℚ) * ∑ i : Fin 3, weightZeroTransition i d e

include hT in
/-- One round of the recursion along one axis: an element of weight zero along axis
  `i` expanded in the generators re-expands with the weight-zero transition matrix
  applied to its coefficients — the nonzero-weight components of the expansion must
  vanish, and the surviving weight-zero part is `weightZeroTransition` acting on `c`. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
  have hsum : x = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ),
            hT.monoComponent i e m :=
          Finset.sum_congr rfl fun e _ => by rw [← hT.eq_sum_monoComponent_univ i e]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ e, c e • hT.monoComponent i e 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ e, c e • hT.monoComponent i e m) hw
      (fun m _ => sum_mem fun e _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i e m))
      (by decide) hsum
  calc x = ∑ e, c e • hT.monoComponent i e 0 := hx0
    _ = ∑ e, c e • ∑ d, ((weightZeroTransition i d e : ℚ) : ℂ) • T d :=
        Finset.sum_congr rfl fun e _ => by rw [hT.monoComponent_zero_eq i e]
    _ = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        exact Finset.sum_congr rfl fun e _ => mul_comm _ _

include hT in
/-- One averaged round of the recursion: an element of weight zero along all three
  axes re-expands with the boost-average matrix `M` applied to its coefficients — the
  average over the axes of `eq_sum_weightZeroTransition_smul`. -/
lemma eq_sum_boostAverageTransition_smul {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
  have hround : ∀ i : Fin 3,
      x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3⁻¹ : ℂ) • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, x := by rw [h3]
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, ∑ d,
          (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
        congrArg (fun y => (3⁻¹ : ℂ) • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [boostAverageTransition, Matrix.of_apply]
        push_cast
        rw [mul_assoc, Finset.sum_mul]

/-!

## D. Sieving the span along the three boost axes

An invariant element has boost weight zero along every axis; three successive
weight-zero extractions cut the span down to the tied pieces of the last axis.

## D.1. Pieces along one axis

-/

/-- The span of the axis-`i` light-cone components of total weight `n`. -/
def boostPiece (i : Fin 3) (n : ℤ) : Submodule ℂ B :=
  ⨆ c ∈ {c : Fin 4 → Fin 4 | (∑ j, lightConeWeight (c j)) = n}, ℂ ∙ hT.lightCone i c

lemma boostPiece_le_boostWeightSubmodule (i : Fin 3) (n : ℤ) :
    hT.boostPiece i n ≤ boostWeightSubmodule repLorentz i n := by
  refine iSup₂_le fun c hc => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact (show (∑ j, lightConeWeight (c j)) = n from hc) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The span regrouped by boost weight: the light-cone components sorted by their
  total weight along the axis. -/
lemma span_eq_iSup_boostPiece (i : Fin 3) :
    hT.span = ⨆ n : ℤ, hT.boostPiece i n := by
  rw [hT.span_eq_lightCone i]
  refine le_antisymm (iSup_le fun c => ?_) (iSup_le fun n => iSup₂_le fun c _ => ?_)
  · exact le_iSup_of_le (∑ s, lightConeWeight (c s)) (le_iSup₂_of_le c rfl le_rfl)
  · exact le_iSup_of_le c le_rfl

/-!

## D.2. Pieces along a second axis

The axis-`i` and axis-`j` light-cone bases are related slot by slot by an invertible
`4 × 4` transition matrix. An axis-`i` piece is therefore covered by axis-`j` pieces
spanned by the light-cone components reachable through nonzero transition coefficients.

-/

/-- The one-slot transition matrix between two light-cone bases: the axis-`i`
  light-cone direction `κ` expanded in the axis-`j` light-cone basis. Rational-valued —
  the entries are `0`, `±2⁻¹` and `±1` — so that vanishing of entries is decidable;
  `coe_lightConeTransition` identifies it with the composite change of basis over `ℂ`. -/
def lightConeTransition (i j : Fin 3) (κ κ' : Fin 4) : ℚ :=
  if j = i then (if κ = κ' then 1 else 0)
  else if j = i + 1 then
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 3 then -1 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 3 then 1 else 0)
    else if κ = 2 then (if κ' = 0 then -2⁻¹ else if κ' = 1 then 2⁻¹ else 0)
    else (if κ' = 2 then 1 else 0)
  else
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 2 then -1 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 2 then 1 else 0)
    else if κ = 2 then (if κ' = 3 then 1 else 0)
    else (if κ' = 0 then -2⁻¹ else if κ' = 1 then 2⁻¹ else 0)

/-- The transition matrix is the composite change of basis: the axis-`i` light-cone
  coefficients composed with the inverse axis-`j` coefficients. -/
lemma coe_lightConeTransition (i j : Fin 3) (κ κ' : Fin 4) :
    (lightConeTransition i j κ κ' : ℂ)
      = ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ * lightConeCoeffInv j μ κ' := by
  fin_cases i <;> fin_cases j <;> fin_cases κ <;> fin_cases κ' <;>
    simp [lightConeTransition, lightConeCoeff, lightConeCoeffInv, Fintype.sum_sum_type,
      Fin.sum_univ_three] <;>
    norm_num

/-- Integer mirror of twice the transition matrix: the entries are `0`, `±1` and `±2`. -/
def lightConeTransitionZ (i j : Fin 3) (κ κ' : Fin 4) : ℤ :=
  if j = i then (if κ = κ' then 2 else 0)
  else if j = i + 1 then
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 3 then -2 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 3 then 2 else 0)
    else if κ = 2 then (if κ' = 0 then -1 else if κ' = 1 then 1 else 0)
    else (if κ' = 2 then 2 else 0)
  else
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 2 then -2 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 2 then 2 else 0)
    else if κ = 2 then (if κ' = 3 then 2 else 0)
    else (if κ' = 0 then -1 else if κ' = 1 then 1 else 0)

/-- The transition matrix is half its integer mirror. -/
lemma coe_lightConeTransition_eq (i j : Fin 3) (κ κ' : Fin 4) :
    ((lightConeTransition i j κ κ' : ℚ) : ℂ)
      = 2⁻¹ * ((lightConeTransitionZ i j κ κ' : ℤ) : ℂ) := by
  rw [lightConeTransition, lightConeTransitionZ]
  split_ifs <;> norm_num

/-- The transition coefficients of a multi-index factor slot by slot. -/
lemma sum_prod_lightConeTransition (i j : Fin 3) (c c' : Fin 4 → Fin 4) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) *
        (∏ s, lightConeCoeffInv j (d s) (c' s))
      = ∏ s, (lightConeTransition i j (c s) (c' s) : ℂ) := by
  calc ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) *
        (∏ s, lightConeCoeffInv j (d s) (c' s))
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
          ∏ s, (lightConeCoeff i (c s) (d s) * lightConeCoeffInv j (d s) (c' s)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ s, ∑ μ : Fin 1 ⊕ Fin 3,
          (lightConeCoeff i (c s) μ * lightConeCoeffInv j μ (c' s)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ s, (lightConeTransition i j (c s) (c' s) : ℂ) :=
        Finset.prod_congr rfl fun s _ => (coe_lightConeTransition i j (c s) (c' s)).symm

/-- The change-of-axis identity: an axis-`i` light-cone component expanded in the
  axis-`j` light-cone basis, with slot-wise transition coefficients. -/
lemma lightCone_eq_sum_lightCone (i j : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c = ∑ c' : Fin 4 → Fin 4,
      (∏ s, (lightConeTransition i j (c s) (c' s) : ℂ)) • hT.lightCone j c' := by
  calc hT.lightCone i c
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) • T d := by
        rw [lightCone]
    _ = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) •
          ∑ c' : Fin 4 → Fin 4,
            (∏ s, lightConeCoeffInv j (d s) (c' s)) • hT.lightCone j c' :=
        Finset.sum_congr rfl fun d _ => by rw [← hT.eq_sum_lightCone j d]
    _ = ∑ c' : Fin 4 → Fin 4, (∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
          (∏ s, lightConeCoeff i (c s) (d s)) *
            (∏ s, lightConeCoeffInv j (d s) (c' s))) • hT.lightCone j c' := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c' _ => (Finset.sum_smul).symm
    _ = _ := Finset.sum_congr rfl fun c' _ => by rw [sum_prod_lightConeTransition]

/-- The second-level pieces: the axis-`j` light-cone components of weight `m` which
  are reachable, slot by slot, from an axis-`i` multi-index of weight `n`. -/
def boostPiece₂ (i j : Fin 3) (n m : ℤ) : Submodule ℂ B :=
  ⨆ c' ∈ {c' : Fin 4 → Fin 4 | (∑ s, lightConeWeight (c' s)) = m ∧
    ∃ c : Fin 4 → Fin 4, (∑ s, lightConeWeight (c s)) = n ∧
      ∀ s, lightConeTransition i j (c s) (c' s) ≠ 0}, ℂ ∙ hT.lightCone j c'

/-- Each second-level piece is contained in the boost-weight space of its weight along
  the second axis. -/
lemma boostPiece₂_le_boostWeightSubmodule (i j : Fin 3) (n m : ℤ) :
    hT.boostPiece₂ i j n m ≤ boostWeightSubmodule repLorentz j m := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact (show (∑ s, lightConeWeight (c' s)) = m from hc'.1) ▸
    hT.lightCone_mem_boostWeightSubmodule j c'

/-- The second-axis covering: each axis-`i` piece is covered by the second-level
  pieces along the axis `j` — the change-of-axis coefficients vanish on unreachable
  multi-indices. -/
lemma boostPiece_le_iSup_boostPiece₂ (i j : Fin 3) (n : ℤ) :
    hT.boostPiece i n ≤ ⨆ m : ℤ, hT.boostPiece₂ i j n m := by
  refine iSup₂_le fun c hc => ?_
  rw [Submodule.span_singleton_le_iff_mem, hT.lightCone_eq_sum_lightCone i j c]
  refine sum_mem fun c' _ => ?_
  by_cases hz : ∀ s, lightConeTransition i j (c s) (c' s) ≠ 0
  · refine Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (∑ s, lightConeWeight (c' s)) ?_)
    rw [boostPiece₂]
    exact Submodule.mem_iSup_of_mem c' (Submodule.mem_iSup_of_mem ⟨rfl, c, hc, hz⟩
      (Submodule.mem_span_singleton_self _))
  · push Not at hz
    obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, Rat.cast_zero]), zero_smul]
    exact Submodule.zero_mem _

/-!

## D.3. Tied pieces along the third axis

Covering the doubly-weight-zero part by spans of whole light-cone components stabilises
along the third axis, so the third round instead splits each generator into its
boost-weight components along the last axis — the tied combinations — and takes the
pieces spanned by those components.

-/

/-- The axis-`j` weight-`m` component of an axis-`i` light-cone component: the partial
  sum of its change-of-axis expansion over the axis-`j` multi-indices of weight `m`. -/
noncomputable def boostComponent (i j : Fin 3) (c : Fin 4 → Fin 4) (m : ℤ) : B :=
  ∑ c' ∈ Finset.univ.filter (fun c' : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c' s)) = m),
    (∏ s, (lightConeTransition i j (c s) (c' s) : ℂ)) • hT.lightCone j c'

/-- Each component is a boost eigenvector of its weight: it is a combination of
  light-cone components of that weight. -/
lemma boostComponent_mem_boostWeightSubmodule (i j : Fin 3) (c : Fin 4 → Fin 4) (m : ℤ) :
    hT.boostComponent i j c m ∈ boostWeightSubmodule repLorentz j m := by
  refine sum_mem fun c' hc' => Submodule.smul_mem _ _ ?_
  exact (Finset.mem_filter.1 hc').2 ▸ hT.lightCone_mem_boostWeightSubmodule j c'

set_option maxRecDepth 10000 in
/-- A light-cone component is the sum of its boost-weight components along any other
  axis: the change-of-axis expansion regrouped by weight. -/
lemma lightCone_eq_sum_boostComponent (i j : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c
      = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ), hT.boostComponent i j c m := by
  rw [hT.lightCone_eq_sum_lightCone i j c]
  exact (Finset.sum_fiberwise_of_maps_to (fun c' _ => sum_lightConeWeight_mem c') _).symm

/-- The tied pieces along the third axis: for each generator of the doubly-weight-zero
  part, the span of its weight-`m` component along the last axis. -/
noncomputable def boostPiece₃ (m : ℤ) : Submodule ℂ B :=
  ⨆ c' ∈ {c' : Fin 4 → Fin 4 | (∑ s, lightConeWeight (c' s)) = 0 ∧
    ∃ c : Fin 4 → Fin 4, (∑ s, lightConeWeight (c s)) = 0 ∧
      ∀ s, lightConeTransition 0 1 (c s) (c' s) ≠ 0},
    ℂ ∙ hT.boostComponent 1 2 c' m

/-- Each tied piece is contained in the boost-weight space of its weight along the last
  axis. -/
lemma boostPiece₃_le_boostWeightSubmodule (m : ℤ) :
    hT.boostPiece₃ m ≤ boostWeightSubmodule repLorentz 2 m := by
  refine iSup₂_le fun c' _ => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact hT.boostComponent_mem_boostWeightSubmodule 1 2 c' m

/-- The third-axis covering: the doubly-weight-zero part is covered by the tied
  pieces along the last axis. -/
lemma boostPiece₂_le_iSup_boostPiece₃ :
    hT.boostPiece₂ 0 1 0 0 ≤ ⨆ m : ℤ, hT.boostPiece₃ m := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem, hT.lightCone_eq_sum_boostComponent 1 2 c']
  refine sum_mem fun m _ => ?_
  refine Submodule.mem_iSup_of_mem m ?_
  rw [boostPiece₃]
  exact Submodule.mem_iSup_of_mem c' (Submodule.mem_iSup_of_mem hc'
    (Submodule.mem_span_singleton_self _))


/-!

## E. The support of the weight-zero tied piece

The weight-zero tied piece only involves components `T d` whose four indices either form
two identical pairs or are all different: the remaining components cancel out of every
tied generator, by a sign involution swapping the two null light-cone directions. The
finite checks are performed by `decide` on the integer mirrors.

## E.1. The null-swap sign involution kills the bad components

-/

/-- The index vectors surviving the three boost sieves: the four indices either split
  into two pairs of identical indices, or are all different. -/
def IsPairedOrDistinct (d : Fin 4 → Fin 1 ⊕ Fin 3) : Prop :=
  (d 0 = d 1 ∧ d 2 = d 3) ∨ (d 0 = d 2 ∧ d 1 = d 3) ∨ (d 0 = d 3 ∧ d 1 = d 2) ∨
    Function.Injective d

instance : DecidablePred IsPairedOrDistinct := fun d =>
  inferInstanceAs (Decidable ((d 0 = d 1 ∧ d 2 = d 3) ∨ (d 0 = d 2 ∧ d 1 = d 3) ∨
    (d 0 = d 3 ∧ d 1 = d 2) ∨ Function.Injective d))

/-- A slot whose fibre has even size shares its direction letter with another slot: the
  fibre is nonempty, so an even fibre has at least two elements. -/
lemma exists_ne_eq_of_even_card (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (h : ∀ μ, Even (Finset.univ.filter fun s => d s = μ).card) (s : Fin 4) :
    ∃ t, t ≠ s ∧ d t = d s := by
  have hmem : s ∈ Finset.univ.filter fun t => d t = d s := by simp
  have hpos : 0 < (Finset.univ.filter fun t => d t = d s).card :=
    Finset.card_pos.2 ⟨s, hmem⟩
  have h1 : 1 < (Finset.univ.filter fun t => d t = d s).card := by
    have := Nat.even_iff.1 (h (d s)); omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases eq_or_ne a s with rfl | hne
  · exact ⟨b, Ne.symm hab, hb⟩
  · exact ⟨a, hne, ha⟩

/-- **Paired-or-distinct is a parity condition on the multiplicities.** Counting how often
  each of the four direction letters occurs among the four slots, the surviving patterns are
  exactly those whose four multiplicities share a parity: all even gives four of a kind or
  two pairs, and all odd forces every multiplicity to be one, four odd numbers summing to
  four only as `1 + 1 + 1 + 1`. Both fours are used, four slots and four letters. -/
lemma isPairedOrDistinct_iff_card_parity (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    IsPairedOrDistinct d ↔
      (∀ μ, Even (Finset.univ.filter fun s => d s = μ).card) ∨
      (∀ μ, Odd (Finset.univ.filter fun s => d s = μ).card) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | hinj)
    · exact Or.inl fun μ => by
        rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four, h1, h2]; split_ifs <;> rfl
    · exact Or.inl fun μ => by
        rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four, h1, h2]; split_ifs <;> rfl
    · exact Or.inl fun μ => by
        rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four, h1, h2]; split_ifs <;> rfl
    · refine Or.inr fun μ => ?_
      have hbij : Function.Bijective d :=
        (Fintype.bijective_iff_injective_and_card d).2 ⟨hinj, by simp⟩
      obtain ⟨s, hs⟩ := hbij.surjective μ
      have hsingle : (Finset.univ.filter fun t => d t = μ) = {s} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hbij.injective (h.trans hs.symm), fun h => h ▸ hs⟩
      rw [hsingle, Finset.card_singleton]
      exact Nat.odd_iff.2 rfl
  · rintro (heven | hodd)
    · -- all fibres even: slot 0 has a partner, and the complementary pair must agree
      obtain ⟨k, hk0, hk⟩ := exists_ne_eq_of_even_card d heven 0
      have pair : ∀ a b c e : Fin 4, (∀ t : Fin 4, t = a ∨ t = b ∨ t = c ∨ t = e) →
          d a = d b → c ≠ e → d c = d e := by
        intro a b c e hall hab hce
        by_contra hne
        obtain ⟨t, ht, htc⟩ := exists_ne_eq_of_even_card d heven c
        obtain ⟨u, hu, hue⟩ := exists_ne_eq_of_even_card d heven e
        have hdc : d c = d a := by
          rcases hall t with rfl | rfl | rfl | rfl
          · exact htc.symm
          · exact htc.symm.trans hab.symm
          · exact absurd rfl ht
          · exact absurd htc.symm hne
        have hde : d e = d a := by
          rcases hall u with rfl | rfl | rfl | rfl
          · exact hue.symm
          · exact hue.symm.trans hab.symm
          · exact absurd hue hne
          · exact absurd rfl hu
        exact hne (hdc.trans hde.symm)
      fin_cases k
      · exact absurd rfl hk0
      · exact Or.inl ⟨hk.symm,
          pair 0 1 2 3 (by intro t; fin_cases t <;> simp) hk.symm (by omega)⟩
      · exact Or.inr (Or.inl ⟨hk.symm,
          pair 0 2 1 3 (by intro t; fin_cases t <;> simp) hk.symm (by omega)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hk.symm,
          pair 0 3 1 2 (by intro t; fin_cases t <;> simp) hk.symm (by omega)⟩))
    · -- all fibres odd: each is exactly 1, so `d` is injective
      have hsum : ∑ μ : Fin 1 ⊕ Fin 3,
          (Finset.univ.filter fun s => d s = μ).card = 4 := by
        rw [← Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_univ (d s))]
        simp
      rw [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three] at hsum
      have h0 := Nat.odd_iff.1 (hodd (Sum.inl 0))
      have h1 := Nat.odd_iff.1 (hodd (Sum.inr 0))
      have h2 := Nat.odd_iff.1 (hodd (Sum.inr 1))
      have h3 := Nat.odd_iff.1 (hodd (Sum.inr 2))
      have hone : ∀ μ, (Finset.univ.filter fun s => d s = μ).card = 1 := by
        intro μ
        rcases μ with a | j
        · rw [Subsingleton.elim a 0]; omega
        · fin_cases j
          · exact (by omega : (Finset.univ.filter fun s => d s = Sum.inr 0).card = 1)
          · exact (by omega : (Finset.univ.filter fun s => d s = Sum.inr 1).card = 1)
          · exact (by omega : (Finset.univ.filter fun s => d s = Sum.inr 2).card = 1)
      refine Or.inr (Or.inr (Or.inr fun s t hst => ?_))
      by_contra hne
      have h2le : 1 < (Finset.univ.filter fun r => d r = d s).card :=
        Finset.one_lt_card.2 ⟨s, by simp, t, by simp [hst], hne⟩
      rw [hone] at h2le
      omega

/-- Parity is the only obstruction: two index vectors whose multiplicities agree in parity
  are paired-or-distinct together. -/
lemma isPairedOrDistinct_congr_of_card_parity {d e : Fin 4 → Fin 1 ⊕ Fin 3}
    (h : ∀ μ, (Finset.univ.filter fun s => d s = μ).card % 2
        = (Finset.univ.filter fun s => e s = μ).card % 2) :
    IsPairedOrDistinct d ↔ IsPairedOrDistinct e := by
  rw [isPairedOrDistinct_iff_card_parity, isPairedOrDistinct_iff_card_parity]
  constructor
  · rintro (hh | hh)
    · exact Or.inl fun μ => Nat.even_iff.2 (by have := h μ; have := Nat.even_iff.1 (hh μ); omega)
    · exact Or.inr fun μ => Nat.odd_iff.2 (by have := h μ; have := Nat.odd_iff.1 (hh μ); omega)
  · rintro (hh | hh)
    · exact Or.inl fun μ => Nat.even_iff.2 (by have := h μ; have := Nat.even_iff.1 (hh μ); omega)
    · exact Or.inr fun μ => Nat.odd_iff.2 (by have := h μ; have := Nat.odd_iff.1 (hh μ); omega)

/-- The swap of the two null light-cone directions. -/
def swap01 : Fin 4 → Fin 4 := fun κ => if κ = 0 then 1 else if κ = 1 then 0 else κ

/-- The sign by which the null swap changes a slot: `-1` exactly on the null-sector
  mismatches. -/
def nuZ (a : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if μ = Sum.inl 0 then (if a = 2 then -1 else 1)
  else if μ = Sum.inr 2 then (if a = 0 ∨ a = 1 then -1 else 1)
  else 1

/-- The null swap is an involution. -/
lemma swap01_swap01 (κ : Fin 4) : swap01 (swap01 κ) = κ := by
  fin_cases κ <;> rfl

/-- The null swap negates the light-cone weight. -/
lemma lightConeWeight_swap01 (κ : Fin 4) :
    lightConeWeight (swap01 κ) = -lightConeWeight κ := by
  fin_cases κ <;> rfl

/-- Null-swap cancellation: a function of light-cone multi-indices which the null swap
  negates sums to zero over the weight-zero multi-indices. The swap preserves the
  weight-zero condition because it negates the total weight, so it is an involution of
  the summation set pairing each term with its negative. Torsion-freeness is needed
  because the involution does have fixed points — the multi-indices whose entries are
  all transverse — and their terms vanish only because `x = -x` forces `x = 0`. Used
  along both axes, in the sign-involution cases of
  `sum_prod_transitionZ_coeffZ_eq_zero` and
  `weightZeroTransition_eq_zero_of_not_isPairedOrDistinct`. -/
lemma sum_weightZero_eq_zero_of_swap01_neg {M : Type*} [AddCommGroup M]
    [IsAddTorsionFree M] (f : (Fin 4 → Fin 4) → M)
    (hf : ∀ c, f (fun s => swap01 (c s)) = -f c) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
      (∑ s, lightConeWeight (c s)) = 0), f c = 0 := by
  refine Finset.sum_involution (fun c _ => fun s => swap01 (c s)) ?_ ?_ ?_ ?_
  · intro c _
    rw [hf c]
    exact add_neg_cancel _
  · intro c _ hne heq
    refine hne ?_
    have h := hf c
    rw [heq] at h
    refine two_nsmul_eq_zero.mp ?_
    rw [two_nsmul]
    exact eq_neg_iff_add_eq_zero.mp h
  · intro c hc
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [show (∑ s, lightConeWeight (swap01 (c s))) = -∑ s, lightConeWeight (c s) from by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => lightConeWeight_swap01 (c s),
      (Finset.mem_filter.1 hc).2, neg_zero]
  · intro c _
    funext s
    exact swap01_swap01 (c s)

/-- The slot identity of the sign involution: swapping the null directions of the
  inner index multiplies the slot factor by the sign `nuZ`. -/
lemma transitionZ_swap01_mul_coeffZ :
    ∀ (a κ : Fin 4) (μ : Fin 1 ⊕ Fin 3),
      lightConeTransitionZ 1 2 a (swap01 κ) * lightConeCoeffZ 2 (swap01 κ) μ
        = nuZ a μ * (lightConeTransitionZ 1 2 a κ * lightConeCoeffZ 2 κ μ) := by
  decide

/-- Weight balance is a parity constraint on the null slots: a weight-zero light-cone
  multi-index uses the two null directions equally often, and so uses an even number of
  them. -/
lemma even_card_null_of_sum_lightConeWeight_eq_zero (c : Fin 4 → Fin 4)
    (hc : (∑ s, lightConeWeight (c s)) = 0) :
    Even (Finset.univ.filter fun s => c s = 0 ∨ c s = 1).card := by
  have hw (κ : Fin 4) :
      lightConeWeight κ = 2 * (if κ = 0 then 1 else 0) - 2 * (if κ = 1 then 1 else 0) := by
    fin_cases κ <;> simp [lightConeWeight]
  have hsum : (2 : ℤ) * ((Finset.univ.filter fun s => c s = 0).card : ℤ)
      - 2 * ((Finset.univ.filter fun s => c s = 1).card : ℤ) = 0 := by
    rw [← hc]
    simp only [hw, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  have hdisj : Disjoint (Finset.univ.filter fun s : Fin 4 => c s = 0)
      (Finset.univ.filter fun s : Fin 4 => c s = 1) :=
    Finset.disjoint_filter.2 fun s _ h0 h1 => by simp [h0] at h1
  have hunion : (Finset.univ.filter fun s => c s = 0 ∨ c s = 1).card
      = (Finset.univ.filter fun s => c s = 0).card
        + (Finset.univ.filter fun s => c s = 1).card := by
    rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj]
  rw [hunion]
  exact ⟨(Finset.univ.filter fun s => c s = 0).card, by omega⟩

/-- The axis-`2` coefficients are sector-block-diagonal: where a slot factor is nonzero,
  the inner light-cone index is null exactly when the outer direction lies in the null
  sector. The transverse directions match one to one instead. -/
lemma null_iff_of_lightConeCoeffZ_ne_zero (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3)
    (h : lightConeCoeffZ 2 κ μ ≠ 0) :
    (μ = Sum.inl 0 ∨ μ = Sum.inr 2) ↔ (κ = 0 ∨ κ = 1) := by
  rcases μ with a | j
  · rw [Subsingleton.elim a 0] at h ⊢
    fin_cases κ <;> simp_all [lightConeCoeffZ]
  · fin_cases j <;> fin_cases κ <;> simp_all [lightConeCoeffZ]

/-- The odd-count case: if the number of null-sector indices of `d` is odd, every
  weight-zero inner index hits a vanishing coefficient. -/
lemma exists_coeffZ_eq_zero_of_odd (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (hodd : Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card)
    (c'' : Fin 4 → Fin 4) (hc'' : (∑ s, lightConeWeight (c'' s)) = 0) :
    ∃ s, lightConeCoeffZ 2 (c'' s) (d s) = 0 := by
  by_contra hne
  push Not at hne
  rw [Finset.filter_congr fun s _ =>
    null_iff_of_lightConeCoeffZ_ne_zero (c'' s) (d s) (hne s)] at hodd
  exact (Nat.not_even_iff_odd.2 hodd)
    (even_card_null_of_sum_lightConeWeight_eq_zero c'' hc'')

/-- On a supported slot, `nuZ` factors into the sign of the outer row and the sign of
  the coordinate column. -/
lemma nuZ_eq_row_sign_mul_column_sign (a : Fin 4) (μ : Fin 1 ⊕ Fin 3)
    (h : ∃ κ, lightConeTransitionZ 1 2 a κ * lightConeCoeffZ 2 κ μ ≠ 0) :
    nuZ a μ =
      (if a = 0 ∨ a = 1 then -1 else 1) *
      (if μ = Sum.inl 0 ∨ μ = Sum.inr 1 then -1 else 1) := by
  obtain ⟨κ, hκ⟩ := h
  rcases μ with b | j
  · rw [Subsingleton.elim b 0] at hκ ⊢
    fin_cases a <;> fin_cases κ <;>
      simp_all [nuZ, lightConeTransitionZ, lightConeCoeffZ]
  · fin_cases j <;> fin_cases a <;> fin_cases κ <;>
      simp_all [nuZ, lightConeTransitionZ, lightConeCoeffZ]

/-- A bad coordinate-index pattern with even null-sector multiplicity has odd
  multiplicity in the column-sign sector. -/
lemma odd_card_inl_zero_or_inr_one_of_not_isPairedOrDistinct
    (d : Fin 4 → Fin 1 ⊕ Fin 3) (hd : ¬IsPairedOrDistinct d)
    (hC : ¬Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card) :
    Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 1).card := by
  rw [isPairedOrDistinct_iff_card_parity] at hd
  let n0 := (Finset.univ.filter fun s => d s = Sum.inl 0).card
  let n1 := (Finset.univ.filter fun s => d s = Sum.inr 0).card
  let n2 := (Finset.univ.filter fun s => d s = Sum.inr 1).card
  let n3 := (Finset.univ.filter fun s => d s = Sum.inr 2).card
  have hsplit (μ ν : Fin 1 ⊕ Fin 3) (hne : μ ≠ ν) :
      (Finset.univ.filter fun s => d s = μ ∨ d s = ν).card
        = (Finset.univ.filter fun s => d s = μ).card
          + (Finset.univ.filter fun s => d s = ν).card := by
    rw [Finset.filter_or, Finset.card_union_of_disjoint]
    exact Finset.disjoint_filter.2 fun s _ hμ hν => hne (hμ.symm.trans hν)
  have hsum : n0 + n1 + n2 + n3 = 4 := by
    have h : ∑ μ : Fin 1 ⊕ Fin 3,
        (Finset.univ.filter fun s => d s = μ).card = 4 := by
      rw [← Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_univ (d s))]
      simp
    rw [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three] at h
    simpa [n0, n1, n2, n3, Nat.add_assoc] using h
  have hnullEven : Even (n0 + n3) := by
    rw [← hsplit (Sum.inl 0) (Sum.inr 2) (by simp)]
    exact Nat.not_odd_iff_even.mp hC
  rw [hsplit (Sum.inl 0) (Sum.inr 1) (by simp), ← Nat.not_even_iff_odd]
  intro hcolumnEven
  apply hd
  have h03 := Nat.even_iff.1 hnullEven
  have h02 := Nat.even_iff.1 hcolumnEven
  have hparity : ∀ μ, (Finset.univ.filter fun s => d s = μ).card % 2 = n0 % 2 := by
    rintro (b | j)
    · rw [Subsingleton.elim b 0]
    · fin_cases j
      · change n1 % 2 = n0 % 2
        omega
      · change n2 % 2 = n0 % 2
        omega
      · change n3 % 2 = n0 % 2
        omega
  rcases Nat.even_or_odd n0 with h0 | h0
  · exact Or.inl fun μ => Nat.even_iff.2 (by rw [hparity μ]; exact Nat.even_iff.1 h0)
  · exact Or.inr fun μ => Nat.odd_iff.2 (by rw [hparity μ]; exact Nat.odd_iff.1 h0)

/-- The parity of the sign involution: over a weight-zero generator, a component that
  is neither two pairs nor all distinct, with no identically-vanishing slot and an even
  null-sector count, carries total sign `-1`. -/
lemma prod_nuZ_eq_neg_one (c' : Fin 4 → Fin 4)
    (hc' : (∑ s, lightConeWeight (c' s)) = 0) (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (hd : ¬IsPairedOrDistinct d)
    (hA : ¬(∃ s, ∀ κ,
      lightConeTransitionZ 1 2 (c' s) κ * lightConeCoeffZ 2 κ (d s) = 0))
    (hC : ¬Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card) :
    (∏ s, nuZ (c' s) (d s)) = -1 := by
  push Not at hA
  have hcolumn :=
    odd_card_inl_zero_or_inr_one_of_not_isPairedOrDistinct d hd hC
  have hrow : Even (Finset.univ.filter fun s => c' s = 0 ∨ c' s = 1).card :=
    even_card_null_of_sum_lightConeWeight_eq_zero c' hc'
  have hfactor (s : Fin 4) :
      nuZ (c' s) (d s) =
        (if c' s = 0 ∨ c' s = 1 then -1 else 1) *
        (if d s = Sum.inl 0 ∨ d s = Sum.inr 1 then -1 else 1) :=
    nuZ_eq_row_sign_mul_column_sign (c' s) (d s) (hA s)
  calc
    (∏ s, nuZ (c' s) (d s)) =
        (∏ s, if c' s = 0 ∨ c' s = 1 then (-1 : ℤ) else 1) *
        (∏ s, if d s = Sum.inl 0 ∨ d s = Sum.inr 1 then (-1 : ℤ) else 1) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => hfactor s
    _ = (-1 : ℤ) ^
        ((Finset.univ.filter fun s => c' s = 0 ∨ c' s = 1).card +
          (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 1).card) := by
      rw [pow_add]
      congr 1 <;>
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    _ = -1 := Odd.neg_one_pow (Even.add_odd hrow hcolumn)

/-- The vanishing of the bad coefficients: over a weight-zero generator, the inner
  transition sum vanishes on every component that is neither two pairs nor all
  distinct — slot by slot when some slot factor vanishes identically or the null-sector
  count is odd, and by the sign involution otherwise. -/
lemma sum_prod_transitionZ_coeffZ_eq_zero (c' : Fin 4 → Fin 4)
    (hc' : (∑ s, lightConeWeight (c' s)) = 0)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) (hd : ¬IsPairedOrDistinct d) :
    (∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
        (∑ s, lightConeWeight (c'' s)) = 0),
      (∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
        (∏ s, lightConeCoeffZ 2 (c'' s) (d s))) = 0 := by
  by_cases hA : ∃ s, ∀ κ, lightConeTransitionZ 1 2 (c' s) κ * lightConeCoeffZ 2 κ (d s) = 0
  · obtain ⟨s, hs⟩ := hA
    refine Finset.sum_eq_zero fun c'' _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (hs (c'' s))
  by_cases hC : Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card
  · refine Finset.sum_eq_zero fun c'' hc'' => ?_
    obtain ⟨s, hs⟩ := exists_coeffZ_eq_zero_of_odd d hC c'' (Finset.mem_filter.1 hc'').2
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [hs, mul_zero]
  have hsgn : (∏ s, nuZ (c' s) (d s)) = -1 := prod_nuZ_eq_neg_one c' hc' d hd hA hC
  have hswap : ∀ c'' : Fin 4 → Fin 4,
      (∏ s, lightConeTransitionZ 1 2 (c' s) (swap01 (c'' s))) *
        (∏ s, lightConeCoeffZ 2 (swap01 (c'' s)) (d s))
      = (∏ s, nuZ (c' s) (d s)) *
        ((∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
          (∏ s, lightConeCoeffZ 2 (c'' s) (d s))) := by
    intro c''
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => transitionZ_swap01_mul_coeffZ (c' s) (c'' s) (d s)
  refine sum_weightZero_eq_zero_of_swap01_neg _ fun c'' => ?_
  rw [hswap c'', hsgn, neg_one_mul]

/-!

## E.2. Sector compatibility and the support of the weight-zero transition

The weight-zero transition out of a paired-or-distinct index vanishes on every bad
index: a sector-incompatible slot kills every summand, and otherwise the null-swap
involution carries sign `-1`.

-/

/-- Two direction letters lie in compatible sectors for the axis-`i` transition: both
  in the null sector, or equal. -/
def SameSlotSector (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : Prop :=
  ((μ = Sum.inl 0 ∨ μ = Sum.inr i) ∧ (ν = Sum.inl 0 ∨ ν = Sum.inr i)) ∨ μ = ν

instance (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : Decidable (SameSlotSector i μ ν) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A sector-incompatible slot annihilates every slot factor. -/
lemma slot_eq_zero_of_not_sameSlotSector :
    ∀ (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3), ¬SameSlotSector i μ ν →
      ∀ κ, lightConeCoeffInvQ i μ κ * (lightConeCoeffZ i κ ν : ℚ) = 0 := by
  decide +kernel

/-- The sign by which the null swap changes an axis-`i` slot factor. -/
def nuSignZ (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  (if μ = Sum.inr i then -1 else 1) * (if ν = Sum.inr i then -1 else 1)

/-- Swapping the null directions multiplies the slot factor by the sign. -/
lemma invQ_swap01_mul_coeffZ_swap01 :
    ∀ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3),
      lightConeCoeffInvQ i μ (swap01 κ) * (lightConeCoeffZ i (swap01 κ) ν : ℚ)
        = (nuSignZ i μ ν : ℚ)
          * (lightConeCoeffInvQ i μ κ * (lightConeCoeffZ i κ ν : ℚ)) := by
  decide +kernel

/-- Sector compatibility transfers every multiplicity parity. Off the null sector the two
  index vectors agree slotwise, so those fibres are equal; the null-sector supports coincide,
  so the two null multiplicities have equal totals, and the axis parity then pins the other. -/
lemma card_mod_two_congr_of_sameSlotSector (i : Fin 3) {d e : Fin 4 → Fin 1 ⊕ Fin 3}
    (hs : ∀ s, SameSlotSector i (e s) (d s))
    (hi : (Finset.univ.filter fun s => d s = Sum.inr i).card % 2
        = (Finset.univ.filter fun s => e s = Sum.inr i).card % 2) (μ : Fin 1 ⊕ Fin 3) :
    (Finset.univ.filter fun s => d s = μ).card % 2
      = (Finset.univ.filter fun s => e s = μ).card % 2 := by
  have hsplit : ∀ f : Fin 4 → Fin 1 ⊕ Fin 3,
      (Finset.univ.filter fun s => f s = Sum.inl 0 ∨ f s = Sum.inr i).card
        = (Finset.univ.filter fun s => f s = Sum.inl 0).card
          + (Finset.univ.filter fun s => f s = Sum.inr i).card := by
    intro f
    rw [Finset.filter_or, Finset.card_union_of_disjoint]
    exact Finset.disjoint_filter.2 fun s _ h0 h1 => by rw [h0] at h1; simp at h1
  have hsupp : (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr i)
      = (Finset.univ.filter fun s => e s = Sum.inl 0 ∨ e s = Sum.inr i) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs s with ⟨he, hd⟩ | hed
    · exact ⟨fun _ => he, fun _ => hd⟩
    · rw [← hed]
  have htot : (Finset.univ.filter fun s => d s = Sum.inl 0).card
        + (Finset.univ.filter fun s => d s = Sum.inr i).card
      = (Finset.univ.filter fun s => e s = Sum.inl 0).card
        + (Finset.univ.filter fun s => e s = Sum.inr i).card := by
    rw [← hsplit d, ← hsplit e, hsupp]
  by_cases hμ0 : μ = Sum.inl 0
  · subst hμ0; omega
  by_cases hμi : μ = Sum.inr i
  · subst hμi; exact hi
  have hfil : (Finset.univ.filter fun s => d s = μ)
      = (Finset.univ.filter fun s => e s = μ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs s with ⟨he, hd⟩ | hed
    · constructor
      · rintro rfl; rcases hd with h | h; exacts [(hμ0 h).elim, (hμi h).elim]
      · rintro rfl; rcases he with h | h; exacts [(hμ0 h).elim, (hμi h).elim]
    · rw [← hed]
  rw [hfil]

/-- The total null-swap sign counts the axis-`i` slots of both index vectors: `nuSignZ` is a
  product of two slot signs, so the product over slots splits into two powers of `-1`. -/
lemma prod_nuSignZ_eq_pow (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    (∏ s, nuSignZ i (e s) (d s))
      = (-1 : ℤ) ^ ((Finset.univ.filter fun s => e s = Sum.inr i).card
          + (Finset.univ.filter fun s => d s = Sum.inr i).card) := by
  have key : ∀ f : Fin 4 → Fin 1 ⊕ Fin 3,
      (∏ s, (if f s = Sum.inr i then (-1 : ℤ) else 1))
        = (-1 : ℤ) ^ (Finset.univ.filter fun s => f s = Sum.inr i).card := by
    intro f
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
  simp only [nuSignZ]
  rw [Finset.prod_mul_distrib, key e, key d, ← pow_add]

/-- The sign of a sector-compatible parity mismatch: a paired-or-distinct column
  index against a bad row index with all slots sector-compatible carries sign `-1`. -/
lemma prod_nuSignZ_eq_neg_one (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3)
    (he : IsPairedOrDistinct e) (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (hd : ¬IsPairedOrDistinct d) (hs : ∀ s, SameSlotSector i (e s) (d s)) :
    (∏ s, nuSignZ i (e s) (d s)) = -1 := by
  rw [prod_nuSignZ_eq_pow]
  refine Odd.neg_one_pow ?_
  rw [Nat.odd_iff]
  by_contra hpar
  refine hd ((isPairedOrDistinct_congr_of_card_parity
    (card_mod_two_congr_of_sameSlotSector i hs ?_)).2 he)
  omega

/-- Support of the weight-zero transition: the transition out of a
  paired-or-distinct index vanishes on every bad index. -/
lemma weightZeroTransition_eq_zero_of_not_isPairedOrDistinct (i : Fin 3)
    {d e : Fin 4 → Fin 1 ⊕ Fin 3} (he : IsPairedOrDistinct e)
    (hd : ¬IsPairedOrDistinct d) : weightZeroTransition i d e = 0 := by
  by_cases hA : ∀ s, SameSlotSector i (e s) (d s)
  · have hsgn := prod_nuSignZ_eq_neg_one i e he d hd hA
    have hswap : ∀ c : Fin 4 → Fin 4,
        (∏ s, lightConeCoeffInvQ i (e s) (swap01 (c s)) *
          (lightConeCoeffZ i (swap01 (c s)) (d s) : ℚ))
        = ((∏ s, nuSignZ i (e s) (d s) : ℤ) : ℚ) *
          ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ) := by
      intro c
      push_cast
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => invQ_swap01_mul_coeffZ_swap01 i (e s) (c s) (d s)
    rw [weightZeroTransition_eq_sum_lightCone]
    refine sum_weightZero_eq_zero_of_swap01_neg _ fun c => ?_
    rw [hswap c, hsgn]
    push_cast
    ring
  · push Not at hA
    obtain ⟨s₀, hs₀⟩ := hA
    rw [weightZeroTransition_eq_sum_lightCone]
    refine Finset.sum_eq_zero fun c _ => ?_
    exact Finset.prod_eq_zero (Finset.mem_univ s₀)
      (slot_eq_zero_of_not_sameSlotSector i (e s₀) (d s₀) hs₀ (c s₀))

/-- Support of the boost average: the average out of a paired-or-distinct index is
  supported on the paired-or-distinct indices. -/
lemma boostAverageTransition_eq_zero_of_not_isPairedOrDistinct
    {d e : Fin 4 → Fin 1 ⊕ Fin 3} (he : IsPairedOrDistinct e)
    (hd : ¬IsPairedOrDistinct d) : boostAverageTransition d e = 0 := by
  simp only [boostAverageTransition, Matrix.of_apply]
  rw [Finset.sum_eq_zero fun i _ =>
    weightZeroTransition_eq_zero_of_not_isPairedOrDistinct i he hd, mul_zero]

/-!

## E.3. The support of the tied piece

-/

/-- The expansion of the weight-zero tied component into monomials: the coefficient
  of each component `T d` is a sixteenth of the integer transition sum. -/
lemma boostComponent_zero_eq (c' : Fin 4 → Fin 4) :
    hT.boostComponent 1 2 c' 0 = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
      ((16⁻¹ : ℂ) * ((∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
          (∑ s, lightConeWeight (c'' s)) = 0),
        (∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
          (∏ s, lightConeCoeffZ 2 (c'' s) (d s)) : ℤ) : ℂ)) • T d := by
  rw [boostComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  simp only [coe_lightConeTransition_eq, ← coe_lightConeCoeffZ, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- The weight-zero tied component of every weight-zero generator is supported on the
  paired-or-distinct components. -/
lemma boostComponent_zero_mem_iSup_pairedOrDistinct (c' : Fin 4 → Fin 4)
    (hc' : (∑ s, lightConeWeight (c' s)) = 0) :
    hT.boostComponent 1 2 c' 0 ∈
      ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d := by
  rw [hT.boostComponent_zero_eq c']
  refine sum_mem fun d _ => ?_
  by_cases hd : IsPairedOrDistinct d
  · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hd (Submodule.mem_span_singleton_self _)))
  · rw [sum_prod_transitionZ_coeffZ_eq_zero c' hc' d hd, Int.cast_zero, mul_zero, zero_smul]
    exact Submodule.zero_mem _

/-- The support of the weight-zero tied piece: it is spanned by the components whose
  four indices either form two identical pairs or are all different. The one-pair and
  three-of-a-kind components cancel out of every tied generator. -/
lemma boostPiece₃_zero_le_iSup_pairedOrDistinct :
    hT.boostPiece₃ 0 ≤
      ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact hT.boostComponent_zero_mem_iSup_pairedOrDistinct c' hc'.1

/-- The span of the paired-or-distinct components. -/
def pairedOrDistinctSubmodule : Submodule ℂ B :=
  ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d


/-!

## F. Averaging over the cyclic rotation of the axes

The cyclic rotation `x → y → z → x` of the spatial axes acts on components by cycling
every index; averaging over it carries the paired-or-distinct span onto the span of
`22` orbit sums, on which the boost average acts by an explicit matrix.

## F.1. Rotation equivariance of the transition matrices

Rotating all direction letters advances the axis of the light-cone coefficients, so
the boost average is invariant under rotating both of its indices.

-/

/-- Rotating the direction letter advances the axis of the light-cone coefficient. -/
lemma lightConeCoeffZ_cycDir :
    ∀ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3),
      lightConeCoeffZ (i + 1) κ (cycDir μ) = lightConeCoeffZ i κ μ := by
  decide

/-- Integer mirror of `lightConeCoeffInvQ`: twice the inverse coefficients, so that
  slot identities can be settled by kernel `decide` over `ℤ`. -/
def lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℤ :=
  if μ = Sum.inl 0 then (if κ = 0 then 1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr i then (if κ = 0 then -1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 2 else 0)
  else (if κ = 3 then 2 else 0)

/-- The integer mirror casts to twice the inverse coefficients. -/
lemma coe_lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℚ) = 2 * lightConeCoeffInvQ i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInvQ]
  split_ifs <;> norm_num

/-- Rotating the direction letter advances the axis of the integer mirror. -/
lemma lightConeCoeffInvZ_cycDir :
    ∀ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4),
      lightConeCoeffInvZ (i + 1) (cycDir μ) κ = lightConeCoeffInvZ i μ κ := by
  decide

/-- Rotating the direction letter advances the axis of the inverse coefficient. -/
lemma lightConeCoeffInvQ_cycDir (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    lightConeCoeffInvQ (i + 1) (cycDir μ) κ = lightConeCoeffInvQ i μ κ := by
  have h := congrArg (fun n : ℤ => (n : ℚ)) (lightConeCoeffInvZ_cycDir i μ κ)
  simp only [coe_lightConeCoeffInvZ] at h
  linarith

/-- Rotation equivariance of the weight-zero transition: rotating both indices
  advances the axis. -/
lemma weightZeroTransition_cycDir (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition (i + 1) (fun s => cycDir (d s)) (fun s => cycDir (e s))
      = weightZeroTransition i d e := by
  rw [weightZeroTransition_eq_sum_lightCone, weightZeroTransition_eq_sum_lightCone]
  refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun s _ => ?_
  rw [lightConeCoeffInvQ_cycDir, lightConeCoeffZ_cycDir]

/-- Rotation invariance of the boost average: the average over the axes is
  invariant under rotating both indices. -/
lemma boostAverageTransition_cycDir (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition (fun s => cycDir (d s)) (fun s => cycDir (e s))
      = boostAverageTransition d e := by
  simp only [boostAverageTransition, Matrix.of_apply]
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin 3)) _ _ fun i =>
    (weightZeroTransition_cycDir i d e).symm).symm

/-- Rotating the column index moves a double rotation to the row index. -/
lemma boostAverageTransition_cycDir_right (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d (fun s => cycDir (e s))
      = boostAverageTransition (fun s => cycDir (cycDir (d s))) e := by
  conv_lhs => rw [show d = (fun s => cycDir (cycDir (cycDir (d s)))) from
    funext fun s => (cycDir_cycDir_cycDir (d s)).symm]
  exact boostAverageTransition_cycDir (fun s => cycDir (cycDir (d s))) e

/-- Rotating the column index twice moves a single rotation to the row index. -/
lemma boostAverageTransition_cycDir_right2 (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = boostAverageTransition (fun s => cycDir (d s)) e := by
  calc boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = boostAverageTransition (fun s => cycDir (cycDir (d s))) (fun s => cycDir (e s)) :=
        boostAverageTransition_cycDir_right d (fun s => cycDir (e s))
    _ = boostAverageTransition (fun s => cycDir (d s)) e :=
        boostAverageTransition_cycDir (fun s => cycDir (d s)) e

/-!

## F.2. The rotational average and orbit sums

-/

/-- The rotation orbit of an index vector: the indices that `d` is carried onto by
  the powers of the cyclic rotation `x → y → z → x` of the rotational average. -/
def rotationIndexSet (d : Fin 4 → Fin 1 ⊕ Fin 3) : Finset (Fin 4 → Fin 1 ⊕ Fin 3) :=
  {d, fun s => cycDir (d s), fun s => cycDir (cycDir (d s))}

/-- The rotational average: the mean of the action of the three powers of the cyclic
  rotation `x → y → z → x`. -/
noncomputable def rotationAverage : B →ₗ[ℂ] B :=
  (3⁻¹ : ℂ) • ((LinearMap.id : B →ₗ[ℂ] B) + repLorentz rotationCycle
    + repLorentz (rotationCycle ^ 2))

/-- The action of the rotational average on the paired-or-distinct span: the image of
  the weight-zero tied piece's support under averaging over the cyclic rotation. -/
noncomputable def rotationSubmodule : Submodule ℂ B :=
  (pairedOrDistinctSubmodule (T := T)).map (rotationAverage (repLorentz := repLorentz))

include hT in
/-- The cyclic rotation acts on components by cycling every index. -/
lemma repLorentz_rotationCycle_apply (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    repLorentz rotationCycle (T d) = T (fun s => cycDir (d s)) := by
  have hcoef : ∀ a : Fin 4 → Fin 1 ⊕ Fin 3,
      (∏ s, (((SL2C.toLorentzGroup rotationCycle).1 (a s) (d s) : ℝ) : ℂ))
        = if a = fun s => cycDir (d s) then 1 else 0 := by
    intro a
    by_cases had : a = fun s => cycDir (d s)
    · rw [if_pos had]
      refine Finset.prod_eq_one fun s _ => ?_
      rw [toLorentzGroup_rotationCycle_apply, if_pos (congrFun had s), Complex.ofReal_one]
    · rw [if_neg had]
      obtain ⟨s, hs⟩ := Function.ne_iff.1 had
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [toLorentzGroup_rotationCycle_apply, if_neg hs, Complex.ofReal_zero]
  rw [hT.repLorentz_T]
  simp only [hcoef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- The sum of a component over its rotation orbit — the un-normalised rotational
  average of `T d`. Its support is `rotationIndexSet d`. -/
noncomputable def rotationOrbitSum (d : Fin 4 → Fin 1 ⊕ Fin 3) : B :=
  T d + T (fun s => cycDir (d s)) + T (fun s => cycDir (cycDir (d s)))

include hT in
/-- The rotational average carries a component to a third of its orbit sum. -/
lemma rotationAverage_apply (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationAverage (repLorentz := repLorentz) (T d)
      = (3⁻¹ : ℂ) • rotationOrbitSum (T := T) d := by
  rw [rotationAverage, sq, map_mul, rotationOrbitSum]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    Module.End.mul_apply, hT.repLorentz_rotationCycle_apply]

include hT in
/-- The rotational average of the paired-or-distinct span, presented by orbit
  sums. -/
lemma rotationSubmodule_eq :
    rotationSubmodule (repLorentz := repLorentz) (T := T)
      = ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d},
          ℂ ∙ rotationOrbitSum (T := T) d := by
  rw [rotationSubmodule, pairedOrDistinctSubmodule]
  simp only [Submodule.map_iSup]
  refine iSup_congr fun d => iSup_congr fun hd => ?_
  rw [Submodule.map_span, Set.image_singleton, hT.rotationAverage_apply d]
  exact Submodule.span_singleton_smul_eq ((by norm_num : (3⁻¹ : ℂ) ≠ 0).isUnit) _

include hT in
/-- Extraction from the rotational average: an element of the averaged span is a
  combination of the orbit sums of the paired-or-distinct components. -/
lemma exists_eq_sum_of_mem_rotationSubmodule {x : B}
    (hx : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T)) :
    ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      x = ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d := by
  rw [hT.rotationSubmodule_eq] at hx
  refine Submodule.iSup_induction
    (motive := fun y => ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      y = ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d)
    (fun d => ⨆ _ : d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d},
      ℂ ∙ rotationOrbitSum (T := T) d) hx ?_ ?_ ?_
  · intro d y hy
    by_cases hd : IsPairedOrDistinct d
    · rw [iSup_pos (show d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}
        from hd)] at hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp [ite_smul, Finset.sum_ite_eq', hd]
    · rw [iSup_neg (show d ∉ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}
        from hd)] at hy
      rw [Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · exact ⟨0, by simp⟩
  · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩

/-!

## F.3. The 22 canonical orbit representatives

`rotationOrbitSum` is constant on rotation orbits, so the extraction over all
paired-or-distinct indices collapses to one term per orbit; `rotationSubset` lists the
canonical representatives explicitly.

-/

omit [Module ℂ B] in
/-- The orbit sum is invariant under rotating the index. -/
lemma rotationOrbitSum_cycDir (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitSum (T := T) (fun s => cycDir (d s)) = rotationOrbitSum (T := T) d := by
  simp only [rotationOrbitSum]
  rw [show (fun s => cycDir (cycDir (cycDir (d s)))) = d from
    funext fun s => cycDir_cycDir_cycDir (d s)]
  abel

/-- An index is the canonical representative of its rotation orbit when its first
  spatial letter, if any, is the first spatial direction. -/
def IsOrbitRep (d : Fin 4 → Fin 1 ⊕ Fin 3) : Prop :=
  (∀ s, d s = Sum.inl 0) ∨ ∃ s, d s = Sum.inr 0 ∧ ∀ s' < s, d s' = Sum.inl 0

instance : DecidablePred IsOrbitRep := fun d =>
  inferInstanceAs (Decidable
    ((∀ s, d s = Sum.inl 0) ∨ ∃ s, d s = Sum.inr 0 ∧ ∀ s' < s, d s' = Sum.inl 0))

/-- The canonical representative of the rotation orbit of an index. -/
def orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) : Fin 4 → Fin 1 ⊕ Fin 3 :=
  if IsOrbitRep d then d
  else if IsOrbitRep (fun s => cycDir (d s)) then fun s => cycDir (d s)
  else fun s => cycDir (cycDir (d s))

omit [Module ℂ B] in
/-- The orbit sum of an index equals that of its canonical representative. -/
lemma rotationOrbitSum_orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitSum (T := T) (orbitRepOf d) = rotationOrbitSum (T := T) d := by
  rw [orbitRepOf]
  split_ifs
  · rfl
  · exact rotationOrbitSum_cycDir (T := T) d
  · exact (rotationOrbitSum_cycDir (T := T) _).trans (rotationOrbitSum_cycDir (T := T) d)

/-- The `22` canonical orbit representatives of the paired-or-distinct indices under
  cyclic rotation. -/
def rotationSubset : Finset (Fin 4 → Fin 1 ⊕ Fin 3) :=
  {![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inl 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 1, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 2, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 1, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inl 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 1, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 2, Sum.inr 0]}

set_option maxRecDepth 10000 in
/-- The canonical representative of a paired-or-distinct index is one of the `22`
  listed representatives. -/
lemma orbitRepOf_mem_rotationSubset :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, IsPairedOrDistinct d →
      orbitRepOf d ∈ rotationSubset := by
  decide

include hT in
/-- Extraction over unique orbit representatives: an element of the rotational
  average is a combination of the orbit sums of the `22` canonical representatives —
  one term per orbit. -/
lemma exists_eq_sum_rotationSubset_of_mem_rotationSubmodule {x : B}
    (hx : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T)) :
    ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      x = ∑ d ∈ rotationSubset, c d • rotationOrbitSum (T := T) d := by
  obtain ⟨c, rfl⟩ := hT.exists_eq_sum_of_mem_rotationSubmodule hx
  refine ⟨fun r => ∑ d ∈ (Finset.univ.filter
      (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d)).filter
      (fun d => orbitRepOf d = r), c d, ?_⟩
  calc ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d
      = ∑ r ∈ rotationSubset, ∑ d ∈ (Finset.univ.filter
            (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d)).filter
            (fun d => orbitRepOf d = r),
          c d • rotationOrbitSum (T := T) d :=
        (Finset.sum_fiberwise_of_maps_to (fun d hd =>
          orbitRepOf_mem_rotationSubset d (Finset.mem_filter.1 hd).2) _).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [show rotationOrbitSum (T := T) r = rotationOrbitSum (T := T) d from
          (Finset.mem_filter.1 hd).2 ▸ rotationOrbitSum_orbitRepOf (T := T) d]

/-!

## F.4. The averaged round on the orbit-sum span

Through the orbit multiplicities `rotationOrbitCoeff`, an averaged round re-expands a
combination of representative orbit sums through the row-orbit sums of the boost
average.

-/

/-- The listed representatives are paired-or-distinct. -/
lemma isPairedOrDistinct_of_mem_rotationSubset :
    ∀ d ∈ rotationSubset, IsPairedOrDistinct d := by
  decide +kernel

/-- Goodness is preserved by rotating the index. -/
lemma isPairedOrDistinct_cycDir (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (hd : IsPairedOrDistinct d) : IsPairedOrDistinct (fun s => cycDir (d s)) := by
  rcases hd with ⟨h01, h23⟩ | ⟨h02, h13⟩ | ⟨h03, h12⟩ | hinj
  · exact Or.inl ⟨congrArg cycDir h01, congrArg cycDir h23⟩
  · exact Or.inr (Or.inl ⟨congrArg cycDir h02, congrArg cycDir h13⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨congrArg cycDir h03, congrArg cycDir h12⟩))
  · exact Or.inr (Or.inr (Or.inr (cycDir_injective.comp hinj)))

/-- The multiplicity with which `d` appears among the three rotations of `e`. -/
def rotationOrbitCoeff (e d : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  (if d = e then 1 else 0) + (if d = (fun s => cycDir (e s)) then 1 else 0)
    + (if d = (fun s => cycDir (cycDir (e s))) then 1 else 0)

/-- Cycles every Lorentz direction in an index vector. -/
private abbrev rotateIndex {ι : Type*} (d : ι → Fin 1 ⊕ Fin 3) :=
  fun s => cycDir (d s)

/-- Cycling every direction three times fixes an index vector. -/
private lemma rotateIndex_three {ι : Type*} (d : ι → Fin 1 ⊕ Fin 3) :
    rotateIndex (rotateIndex (rotateIndex d)) = d := by
  funext s
  exact cycDir_cycDir_cycDir (d s)

/-- Two consecutive members of a rotation orbit can both be canonical only when they coincide. -/
private lemma isOrbitRep_rotateIndex_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hd : IsOrbitRep d) (hr : IsOrbitRep (rotateIndex d)) : rotateIndex d = d := by
  rcases hd with hall | ⟨s, hs, hbefore⟩
  · funext s
    simp [rotateIndex, hall s]
  · exfalso
    rcases hr with hall | ⟨t, ht, htbefore⟩
    · have h := hall s
      simp [rotateIndex, hs] at h
    · obtain hlt | heq | hgt := lt_trichotomy t s
      · have h := ht
        simp [rotateIndex, hbefore t hlt] at h
      · subst t
        simp [rotateIndex, hs] at ht
      · have h := htbefore s hgt
        simp [rotateIndex, hs] at h

/-- Canonical representatives two rotations apart coincide. -/
private lemma isOrbitRep_rotateIndex_rotateIndex_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hd : IsOrbitRep d) (hr : IsOrbitRep (rotateIndex (rotateIndex d))) :
    rotateIndex (rotateIndex d) = d := by
  have h := isOrbitRep_rotateIndex_eq_self hr
    (show IsOrbitRep (rotateIndex (rotateIndex (rotateIndex d))) by
      simpa only [rotateIndex_three] using hd)
  rw [rotateIndex_three] at h
  exact h.symm

/-- A canonical index is its own chosen orbit representative. -/
private lemma orbitRepOf_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3} (hd : IsOrbitRep d) :
    orbitRepOf d = d := by
  simp [orbitRepOf, hd]

/-- The representative chosen from the first rotation of a canonical index is that index. -/
private lemma orbitRepOf_rotateIndex_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hd : IsOrbitRep d) : orbitRepOf (rotateIndex d) = d := by
  rw [orbitRepOf]
  split_ifs with h1 h2
  · exact isOrbitRep_rotateIndex_eq_self hd h1
  · exact isOrbitRep_rotateIndex_rotateIndex_eq_self hd h2
  · exact rotateIndex_three d

/-- The representative chosen from the second rotation of a canonical index is that index. -/
private lemma orbitRepOf_rotateIndex_rotateIndex_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hd : IsOrbitRep d) : orbitRepOf (rotateIndex (rotateIndex d)) = d := by
  rw [orbitRepOf]
  split_ifs with h1 h2
  · exact isOrbitRep_rotateIndex_rotateIndex_eq_self hd h1
  · exact rotateIndex_three d
  · exfalso
    apply h2
    rw [show (fun s => cycDir (cycDir (cycDir (d s)))) = d from
      funext fun s => cycDir_cycDir_cycDir (d s)]
    exact hd

/-- Cyclically shifting the three displayed members of a rotation orbit does not change its set. -/
private lemma rotationIndexSet_rotateIndex (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationIndexSet (rotateIndex d) = rotationIndexSet d := by
  change rotationIndexSet (fun s => cycDir (d s)) = rotationIndexSet d
  ext e
  simp only [rotationIndexSet, Finset.mem_insert, Finset.mem_singleton]
  rw [show (fun s => cycDir (cycDir (cycDir (d s)))) = d from
    funext fun s => cycDir_cycDir_cycDir (d s)]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- A rotation-fixed index has no spatial directions and is therefore canonical. -/
private lemma isOrbitRep_of_rotateIndex_eq_self {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (h : rotateIndex d = d) : IsOrbitRep d := by
  left
  intro s
  have hs := congrFun h s
  rcases hds : d s with x | x
  · congr 1
    exact Subsingleton.elim _ _
  · simp only [rotateIndex, hds, cycDir_inr, Sum.inr.injEq] at hs
    fin_cases x <;> norm_num at hs

/-- A nonzero orbit coefficient says that the index is one of the three displayed rotations. -/
private lemma eq_or_eq_rotateIndex_or_eq_rotateIndex_rotateIndex_of_rotationOrbitCoeff_ne_zero
    {e d : Fin 4 → Fin 1 ⊕ Fin 3} (h : rotationOrbitCoeff e d ≠ 0) :
    d = e ∨ d = rotateIndex e ∨ d = rotateIndex (rotateIndex e) := by
  by_contra hn
  push Not at hn
  simp [rotationOrbitCoeff, hn] at h

/-- Every explicitly listed representative satisfies the structural canonicality predicate. -/
private lemma isOrbitRep_of_mem_rotationSubset :
    ∀ r ∈ rotationSubset, IsOrbitRep r := by
  set_option maxRecDepth 10000 in
    decide

/-- Every index in the rotation orbit of a canonical representative chooses that representative. -/
private lemma orbitRepOf_eq_of_isOrbitRep_of_rotationOrbitCoeff_ne_zero
    {r d : Fin 4 → Fin 1 ⊕ Fin 3} (hr : IsOrbitRep r)
    (h : rotationOrbitCoeff r d ≠ 0) : orbitRepOf d = r := by
  rcases eq_or_eq_rotateIndex_or_eq_rotateIndex_rotateIndex_of_rotationOrbitCoeff_ne_zero h
    with rfl | rfl | rfl
  · exact orbitRepOf_eq_self hr
  · exact orbitRepOf_rotateIndex_eq_self hr
  · exact orbitRepOf_rotateIndex_rotateIndex_eq_self hr

/-- Only members of the orbit of a listed representative meet its indicator. -/
lemma orbitRepOf_eq_of_rotationOrbitCoeff_ne_zero (r : Fin 4 → Fin 1 ⊕ Fin 3)
    (hr : r ∈ rotationSubset) (d : Fin 4 → Fin 1 ⊕ Fin 3)
    (h : rotationOrbitCoeff r d ≠ 0) : orbitRepOf d = r := by
  exact orbitRepOf_eq_of_isOrbitRep_of_rotationOrbitCoeff_ne_zero
    (isOrbitRep_of_mem_rotationSubset r hr) h

/-- The orbit of the canonical representative is the orbit. -/
lemma rotationIndexSet_orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationIndexSet (orbitRepOf d) = rotationIndexSet d := by
  rw [orbitRepOf]
  split_ifs
  · rfl
  · exact rotationIndexSet_rotateIndex d
  · exact (rotationIndexSet_rotateIndex (rotateIndex d)).trans (rotationIndexSet_rotateIndex d)

/-- The multiplicity of an index in its own orbit: `3` on a rotation-fixed index and
  `1` otherwise. -/
lemma rotationOrbitCoeff_orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitCoeff (orbitRepOf d) d =
      if (fun s => cycDir (d s)) = d then 3 else 1 := by
  by_cases hfix : (fun s => cycDir (d s)) = d
  · rw [if_pos hfix, orbitRepOf_eq_self (isOrbitRep_of_rotateIndex_eq_self hfix)]
    have h2 : (fun s => cycDir (cycDir (d s))) = d := by
      funext s
      exact (congrArg cycDir (congrFun hfix s)).trans (congrFun hfix s)
    simp [rotationOrbitCoeff, hfix, h2]
  · rw [if_neg hfix]
    obtain ⟨h2, _⟩ := cycDir_orbit_distinct d hfix
    have hfix' : d ≠ (fun s => cycDir (d s)) := Ne.symm hfix
    have h2' : d ≠ (fun s => cycDir (cycDir (d s))) := Ne.symm h2
    have h3 : (fun s => cycDir (cycDir (cycDir (d s)))) = d :=
      funext fun s => cycDir_cycDir_cycDir (d s)
    have h4 : (fun s => cycDir (cycDir (cycDir (cycDir (d s))))) =
        (fun s => cycDir (d s)) := by
      funext s
      rw [cycDir_cycDir_cycDir]
    rw [orbitRepOf]
    split_ifs
    · simp [rotationOrbitCoeff, hfix', h2']
    · simp [rotationOrbitCoeff, hfix', h2', h3]
    · simp [rotationOrbitCoeff, hfix', h2', h3, h4]

/-- The orbit indicator of a good index vanishes on every bad index. -/
lemma rotationOrbitCoeff_eq_zero {r d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hr : IsPairedOrDistinct r) (hd : ¬IsPairedOrDistinct d) :
    rotationOrbitCoeff r d = 0 := by
  have h1 : ¬(d = r) := fun h => hd (by rw [h]; exact hr)
  have h2 : ¬(d = fun s => cycDir (r s)) := fun h =>
    hd (by rw [h]; exact isPairedOrDistinct_cycDir r hr)
  have h3 : ¬(d = fun s => cycDir (cycDir (r s))) := fun h =>
    hd (by rw [h]; exact isPairedOrDistinct_cycDir _ (isPairedOrDistinct_cycDir r hr))
  rw [rotationOrbitCoeff, if_neg h1, if_neg h2, if_neg h3]
  norm_num

/-- Sums over the orbit of the representative: for any weighting, the sum over the
  orbit of the canonical representative times the multiplicity equals the plain sum
  over the three rotations. -/
lemma sum_rotationIndexSet_orbitRepOf_mul (f : (Fin 4 → Fin 1 ⊕ Fin 3) → ℚ)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    (∑ d' ∈ rotationIndexSet (orbitRepOf d), f d')
        * ((rotationOrbitCoeff (orbitRepOf d) d : ℤ) : ℚ)
      = f d + f (fun s => cycDir (d s)) + f (fun s => cycDir (cycDir (d s))) := by
  rw [rotationIndexSet_orbitRepOf d, rotationOrbitCoeff_orbitRepOf d]
  by_cases hfix : (fun s => cycDir (d s)) = d
  · have h2 : (fun s => cycDir (cycDir (d s))) = d := by
      funext s
      rw [congrFun hfix s, congrFun hfix s]
    rw [rotationIndexSet, if_pos hfix, hfix, h2,
      show ({d, d, d} : Finset (Fin 4 → Fin 1 ⊕ Fin 3)) = {d} from by simp,
      Finset.sum_singleton]
    push_cast
    ring
  · obtain ⟨h31, h32⟩ := cycDir_orbit_distinct d hfix
    rw [rotationIndexSet, if_neg hfix,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h => hfix h.symm, fun h => h31 h.symm⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact fun h => h32 h.symm),
      Finset.sum_singleton]
    push_cast
    ring

/-- The rotated columns collapse onto the representatives: for a good column index,
  the sum of the boost average over the three rotated columns equals the
  representative-indexed combination of its row-orbit sums. -/
lemma boostAverageTransition_orbit_eq (e : Fin 4 → Fin 1 ⊕ Fin 3)
    (he : IsPairedOrDistinct e) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d e + boostAverageTransition d (fun s => cycDir (e s))
        + boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = ∑ r ∈ rotationSubset,
          (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
            * ((rotationOrbitCoeff r d : ℤ) : ℚ) := by
  by_cases hd : IsPairedOrDistinct d
  · have hsingle : (∑ r ∈ rotationSubset,
        (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
          * ((rotationOrbitCoeff r d : ℤ) : ℚ))
        = (∑ d' ∈ rotationIndexSet (orbitRepOf d), boostAverageTransition d' e)
          * ((rotationOrbitCoeff (orbitRepOf d) d : ℤ) : ℚ) :=
      Finset.sum_eq_single_of_mem _ (orbitRepOf_mem_rotationSubset d hd)
        (fun r hr hne => by
          rcases eq_or_ne (rotationOrbitCoeff r d) 0 with h0 | h0
          · rw [h0]
            push_cast
            ring
          · exact absurd (orbitRepOf_eq_of_rotationOrbitCoeff_ne_zero r hr d h0).symm hne)
    rw [hsingle,
      sum_rotationIndexSet_orbitRepOf_mul (fun d' => boostAverageTransition d' e) d,
      boostAverageTransition_cycDir_right, boostAverageTransition_cycDir_right2]
    ring
  · have hs1 := isPairedOrDistinct_cycDir e he
    have hs2 := isPairedOrDistinct_cycDir _ hs1
    have hz : (∑ r ∈ rotationSubset,
        (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
          * ((rotationOrbitCoeff r d : ℤ) : ℚ)) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [rotationOrbitCoeff_eq_zero
          (isPairedOrDistinct_of_mem_rotationSubset r hr) hd]
        push_cast
        ring
    rw [hz, boostAverageTransition_eq_zero_of_not_isPairedOrDistinct he hd,
      boostAverageTransition_eq_zero_of_not_isPairedOrDistinct hs1 hd,
      boostAverageTransition_eq_zero_of_not_isPairedOrDistinct hs2 hd]
    norm_num

/-- Orbit-sum expansions in components: a combination of orbit sums over the
  representatives, expanded into the generators through the orbit indicator. -/
lemma sum_rotationSubset_smul_rotationOrbitSum (b : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) :
    ∑ d ∈ rotationSubset, b d • rotationOrbitSum (T := T) d
      = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (∑ d ∈ rotationSubset, b d * ((rotationOrbitCoeff d e : ℤ) : ℂ)) • T e := by
  calc ∑ d ∈ rotationSubset, b d • rotationOrbitSum (T := T) d
      = ∑ d ∈ rotationSubset, ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (b d * ((rotationOrbitCoeff d e : ℤ) : ℂ)) • T e := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [rotationOrbitSum]
        simp [rotationOrbitCoeff, apply_ite (fun n : ℤ => (n : ℂ)), mul_add, add_smul,
          mul_ite, ite_smul, Finset.sum_add_distrib, Finset.sum_ite_eq', smul_add]
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => (Finset.sum_smul).symm

include hT in
/-- One averaged round at orbit level: an element of weight zero along all three
  axes expanded over the orbit sums of the representatives re-expands through the
  row-orbit sums of the boost average — the matrix of the boost average acting on the
  orbit-sum span. -/
lemma eq_sum_boostAverageTransition_of_mem_rotationSubset {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ d ∈ rotationSubset, c d • rotationOrbitSum (T := T) d)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d ∈ rotationSubset, (∑ e ∈ rotationSubset,
      ((∑ d' ∈ rotationIndexSet d, boostAverageTransition d' e : ℚ) : ℂ) * c e)
        • rotationOrbitSum (T := T) d := by
  have hxT := hx.trans (sum_rotationSubset_smul_rotationOrbitSum (T := T) c)
  have hround := hT.eq_sum_boostAverageTransition_smul _ hxT hw
  rw [hround, sum_rotationSubset_smul_rotationOrbitSum (T := T)]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  calc ∑ e : Fin 4 → Fin 1 ⊕ Fin 3, ((boostAverageTransition d e : ℚ) : ℂ)
        * (∑ r ∈ rotationSubset, c r * ((rotationOrbitCoeff r e : ℤ) : ℂ))
      = ∑ r ∈ rotationSubset, c r * ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          ((boostAverageTransition d e : ℚ) : ℂ) * ((rotationOrbitCoeff r e : ℤ) : ℂ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = ∑ r ∈ rotationSubset, c r
          * ((boostAverageTransition d r + boostAverageTransition d (fun s => cycDir (r s))
            + boostAverageTransition d (fun s => cycDir (cycDir (r s))) : ℚ) : ℂ) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        congr 1
        push_cast
        simp [rotationOrbitCoeff, apply_ite (fun n : ℤ => (n : ℂ)), mul_add, mul_ite,
          Finset.sum_add_distrib, Finset.sum_ite_eq']
    _ = ∑ r ∈ rotationSubset, c r * ((∑ ρ ∈ rotationSubset,
          (∑ d' ∈ rotationIndexSet ρ, boostAverageTransition d' r)
            * ((rotationOrbitCoeff ρ d : ℤ) : ℚ) : ℚ) : ℂ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [boostAverageTransition_orbit_eq r
          (isPairedOrDistinct_of_mem_rotationSubset r hr) d]
    _ = _ := by
        push_cast
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring

/-!

## G. The boost average as an integer `22 × 22` matrix

The representatives are enumerated by `Fin 22`; `48` times the row-orbit sums of the
boost average form an integer matrix computed directly from the integer mirrors.

## G.1. Enumerating the representatives

-/

/-- The enumeration of the `22` canonical orbit representatives, in the order of
  `rotationSubset`. -/
def orbitRep : Fin 22 → Fin 4 → Fin 1 ⊕ Fin 3 :=
  ![![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inl 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 1, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 2, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 1, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inl 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 1, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 2, Sum.inr 0]]

/-- The enumeration of the representatives is injective. -/
lemma orbitRep_injective : Function.Injective orbitRep := by
  decide +kernel

/-- The set of representatives is the image of the enumeration. -/
lemma rotationSubset_eq_image :
    rotationSubset = Finset.univ.image orbitRep := by
  decide +kernel

/-- Sums over the representatives reindexed through the enumeration. -/
lemma sum_rotationSubset {β : Type*} [AddCommMonoid β]
    (f : (Fin 4 → Fin 1 ⊕ Fin 3) → β) :
    ∑ d ∈ rotationSubset, f d = ∑ k : Fin 22, f (orbitRep k) := by
  rw [rotationSubset_eq_image, Finset.sum_image fun k _ k' _ h => orbitRep_injective h]

/-!

## G.2. The closed form of the integer weight-zero transition

The balanced-sector convolution collapses slot by slot, by induction on the slots:
transverse slots contribute a diagonal `2`, sector-incompatible slots kill the entry,
and the null slots fold their signs through `balancedSymZ`.

-/

/-- Integer mirror of `slotTransition`: twice its value, in closed form. On the two
  null sectors it is supported on the axis-`i` block `{t, xᵢ}` — the raising sector
  `κ = 0` carries the sign matrix `[[1, -1], [-1, 1]]`, the lowering sector `κ = 1` the
  all-ones matrix — and the transverse sector `κ = 2` is twice the identity on the two
  transverse directions. `slotTransitionZ_eq_sum` recovers it as the
  `lightConeCoeffInvZ · lightConeCoeffZ` composite summed over the sector. -/
def slotTransitionZ (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 2 then (if μ = ν ∧ μ ≠ Sum.inl 0 ∧ μ ≠ Sum.inr i then 2 else 0)
  else if (μ = Sum.inl 0 ∨ μ = Sum.inr i) ∧ (ν = Sum.inl 0 ∨ ν = Sum.inr i) then
    (if κ = 0 then (if μ = Sum.inr i then -1 else 1) * (if ν = Sum.inr i then -1 else 1)
    else 1)
  else 0

/-- The closed-form integer slot matrix is the sector sum of the coefficient
  composites. -/
lemma slotTransitionZ_eq_sum (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    slotTransitionZ i κ μ ν
      = ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
        lightConeCoeffInvZ i μ κ' * lightConeCoeffZ i κ' ν := by
  decide +revert

/-- A direction letter lies in the axis-`i` null sector: time or the axis direction. -/
def InSector (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Prop := μ = Sum.inl 0 ∨ μ = Sum.inr i

instance (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Decidable (InSector i μ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The balanced fold of a list of signs: the sum, over the raise/lower assignments of
  the listed slots whose weights total `m`, of the products of the raising signs. -/
def balancedSymZ : ℤ → List ℤ → ℤ
  | m, [] => if m = 0 then 1 else 0
  | m, ε :: l => ε * balancedSymZ (m - 2) l + balancedSymZ (m + 2) l

/-- The null-swap signs of the null-sector slots, in slot order. -/
def sectorSigns (i : Fin 3) : {n : ℕ} → (d e : Fin n → Fin 1 ⊕ Fin 3) → List ℤ
  | 0, _, _ => []
  | _ + 1, d, e =>
    if InSector i (e 0) then
      nuSignZ i (e 0) (d 0) :: sectorSigns i (Fin.tail d) (Fin.tail e)
    else sectorSigns i (Fin.tail d) (Fin.tail e)

/-- The number of slots outside the axis-`i` null sector. -/
def transverseCount (i : Fin 3) : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → ℕ
  | 0, _ => 0
  | _ + 1, e => (if InSector i (e 0) then 0 else 1) + transverseCount i (Fin.tail e)

/-- The weight-`m` integer transition over `n` slots, for the slot-peeling induction. -/
def weightTransitionZAux (i : Fin 3) {n : ℕ} (d e : Fin n → Fin 1 ⊕ Fin 3) (m : ℤ) : ℤ :=
  ∑ w : Fin n → Fin 3, if (∑ s, sectorWeight (w s)) = m then
    ∏ s, slotTransitionZ i (w s) (e s) (d s) else 0

lemma slotTransitionZ_raise_of_sector {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hμ : InSector i μ) (hν : InSector i ν) :
    slotTransitionZ i 0 μ ν = nuSignZ i μ ν := by
  rw [slotTransitionZ, nuSignZ, if_neg (by simp), if_pos ⟨hμ, hν⟩, if_pos rfl]

lemma slotTransitionZ_lower_of_sector {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hμ : InSector i μ) (hν : InSector i ν) :
    slotTransitionZ i 1 μ ν = 1 := by
  rw [slotTransitionZ, if_neg (by simp), if_pos ⟨hμ, hν⟩, if_neg (by simp)]

lemma slotTransitionZ_transverse_of_sector {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hμ : InSector i μ) :
    slotTransitionZ i 2 μ ν = 0 := by
  rw [slotTransitionZ, if_pos rfl, if_neg]
  rintro ⟨-, h1, h2⟩
  rcases hμ with h | h
  exacts [h1 h, h2 h]

lemma slotTransitionZ_null_of_not_sector_left {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hμ : ¬InSector i μ) (κ : Fin 3) (hκ : κ ≠ 2) :
    slotTransitionZ i κ μ ν = 0 := by
  rw [slotTransitionZ, if_neg hκ, if_neg]
  exact fun h => hμ h.1

lemma slotTransitionZ_null_of_not_sector_right {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hν : ¬InSector i ν) (κ : Fin 3) (hκ : κ ≠ 2) :
    slotTransitionZ i κ μ ν = 0 := by
  rw [slotTransitionZ, if_neg hκ, if_neg]
  exact fun h => hν h.2

lemma slotTransitionZ_transverse_of_not_sector {i : Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (hμ : ¬InSector i μ) :
    slotTransitionZ i 2 μ ν = if μ = ν then 2 else 0 := by
  rw [slotTransitionZ, if_pos rfl]
  simp only [InSector, not_or] at hμ
  by_cases h : μ = ν
  · rw [if_pos ⟨h, hμ.1, hμ.2⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

lemma weightTransitionZAux_nil (i : Fin 3) (d e : Fin 0 → Fin 1 ⊕ Fin 3) (m : ℤ) :
    weightTransitionZAux i d e m = if m = 0 then 1 else 0 := by
  rw [weightTransitionZAux, Fintype.sum_unique]
  simp [eq_comm]

lemma weightTransitionZAux_succ (i : Fin 3) {n : ℕ} (d e : Fin (n + 1) → Fin 1 ⊕ Fin 3)
    (m : ℤ) :
    weightTransitionZAux i d e m
      = slotTransitionZ i 0 (e 0) (d 0)
          * weightTransitionZAux i (Fin.tail d) (Fin.tail e) (m - 2)
        + slotTransitionZ i 1 (e 0) (d 0)
          * weightTransitionZAux i (Fin.tail d) (Fin.tail e) (m + 2)
        + slotTransitionZ i 2 (e 0) (d 0)
          * weightTransitionZAux i (Fin.tail d) (Fin.tail e) m := by
  rw [weightTransitionZAux,
    ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)), Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.sum_univ_zero, add_zero]
  simp only [show sectorWeight 0 = 2 from rfl, show sectorWeight (Fin.succ 0) = -2 from rfl,
    show sectorWeight ((Fin.succ 0).succ) = 0 from rfl]
  rw [weightTransitionZAux, weightTransitionZAux, weightTransitionZAux, add_assoc]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [mul_ite, mul_zero]
      exact if_congr (by omega) rfl rfl
  · congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by
        rw [mul_ite, mul_zero]
        exact if_congr (by omega) rfl rfl
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by
        rw [mul_ite, mul_zero]
        exact if_congr (by omega) rfl rfl

theorem weightTransitionZAux_eq_closed (i : Fin 3) :
    ∀ {n : ℕ} (d e : Fin n → Fin 1 ⊕ Fin 3) (m : ℤ),
    weightTransitionZAux i d e m
      = if ∀ s, SameSlotSector i (e s) (d s) then
          2 ^ transverseCount i e * balancedSymZ m (sectorSigns i d e)
        else 0
  | 0, d, e, m => by
    rw [weightTransitionZAux_nil, if_pos (fun s => s.elim0)]
    simp [transverseCount, sectorSigns, balancedSymZ]
  | n + 1, d, e, m => by
    rw [weightTransitionZAux_succ,
      weightTransitionZAux_eq_closed i (Fin.tail d) (Fin.tail e) (m - 2),
      weightTransitionZAux_eq_closed i (Fin.tail d) (Fin.tail e) (m + 2),
      weightTransitionZAux_eq_closed i (Fin.tail d) (Fin.tail e) m]
    simp only [Fin.forall_fin_succ]
    by_cases htail : ∀ s : Fin n, SameSlotSector i (Fin.tail e s) (Fin.tail d s)
    case neg =>
      rw [if_neg htail, if_neg htail, if_neg htail, if_neg (fun h => htail h.2)]
      ring
    case pos =>
      rw [if_pos htail, if_pos htail, if_pos htail]
      by_cases he : InSector i (e 0)
      · by_cases hd : InSector i (d 0)
        · rw [slotTransitionZ_raise_of_sector he hd, slotTransitionZ_lower_of_sector he hd,
            slotTransitionZ_transverse_of_sector he, if_pos ⟨Or.inl ⟨he, hd⟩, htail⟩]
          simp only [transverseCount, if_pos he, zero_add, sectorSigns, balancedSymZ]
          ring
        · rw [slotTransitionZ_null_of_not_sector_right hd 0 (by simp),
            slotTransitionZ_null_of_not_sector_right hd 1 (by simp),
            slotTransitionZ_transverse_of_sector he, if_neg ?_]
          · ring
          · rintro ⟨⟨-, hd'⟩ | heq, -⟩
            exacts [hd hd', hd (heq ▸ he)]
      · by_cases heq : e 0 = d 0
        · rw [slotTransitionZ_null_of_not_sector_left he 0 (by simp),
            slotTransitionZ_null_of_not_sector_left he 1 (by simp),
            slotTransitionZ_transverse_of_not_sector he, if_pos heq,
            if_pos ⟨Or.inr heq, htail⟩]
          simp only [transverseCount, if_neg he, sectorSigns]
          rw [pow_add, pow_one]
          ring
        · rw [slotTransitionZ_null_of_not_sector_left he 0 (by simp),
            slotTransitionZ_null_of_not_sector_left he 1 (by simp),
            slotTransitionZ_transverse_of_not_sector he, if_neg heq, if_neg ?_]
          · ring
          · rintro ⟨⟨he', -⟩ | h, -⟩
            exacts [he he', heq h]

/-- Integer mirror of the weight-zero transition: sixteen times its value, in closed
  form — zero unless every slot is sector-compatible, and otherwise a power of two from
  the transverse slots times the balanced symmetric fold of the null-sector signs.
  `weightZeroTransitionZ_eq_sum_sector` recovers the balanced-sector convolution of the
  integer slot matrices. -/
def weightZeroTransitionZ (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  if ∀ s, SameSlotSector i (e s) (d s) then
    2 ^ transverseCount i e * balancedSymZ 0 (sectorSigns i d e)
  else 0

/-- The closed-form integer weight-zero transition as the balanced-sector convolution
  of the integer slot matrices. -/
lemma weightZeroTransitionZ_eq_sum_sector (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    weightZeroTransitionZ i d e
      = ∑ w ∈ Finset.univ.filter (fun w : Fin 4 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
        ∏ s, slotTransitionZ i (w s) (e s) (d s) := by
  rw [weightZeroTransitionZ, ← weightTransitionZAux_eq_closed, weightTransitionZAux,
    Finset.sum_filter]


/-- The integer weight-zero transition as a light-cone sum. -/
lemma weightZeroTransitionZ_eq_sum_lightCone (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    weightZeroTransitionZ i d e
      = ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, lightConeCoeffInvZ i (e s) (c s) * lightConeCoeffZ i (c s) (d s) := by
  rw [weightZeroTransitionZ_eq_sum_sector]
  simp only [slotTransitionZ_eq_sum]
  exact (sum_weightZero_eq_sum_sector
    (fun s κ => lightConeCoeffInvZ i (e s) κ * lightConeCoeffZ i κ (d s))).symm



/-- The integer mirror casts to sixteen times the weight-zero transition. -/
lemma coe_weightZeroTransitionZ (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    ((weightZeroTransitionZ i d e : ℤ) : ℚ) = 16 * weightZeroTransition i d e := by
  rw [weightZeroTransitionZ_eq_sum_lightCone, weightZeroTransition_eq_sum_lightCone]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc ∏ s, ((lightConeCoeffInvZ i (e s) (c s) : ℤ) : ℚ)
        * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)
      = ∏ s, 2 * (lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [coe_lightConeCoeffInvZ]
        ring
    _ = 16 * ∏ s, lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        norm_num [Finset.card_univ]

/-!

## G.3. The integer matrix of the averaged round

-/

/-- The boost average on the orbit-sum span, as an integer matrix: `48` times the
  row-orbit sums of the boost average between representatives, in explicit form.
  `boostAverageOrbitZ_eq_sum` identifies the entries with the row-orbit sums of the
  integer weight-zero transitions. -/
def boostAverageOrbitZ : Matrix (Fin 22) (Fin 22) ℤ :=
  !![18, -2, -2, -2, 0, 0, -2, -2, 0, 0, -2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -6, 22, -2, -2, 0, 0, -2, -2, 0, 0, 6, -2, -8, -8, 0, 0, 0, 0, 0, 0, 0, 0;
    -6, -2, 22, -2, 0, 0, -2, 6, 0, 0, -2, -2, 0, 0, 0, -8, 0, 0, 0, -8, 0, 0;
    -6, -2, -2, 22, 0, 0, 6, -2, 0, 0, -2, -2, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8;
    0, 0, 0, 0, 24, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0;
    0, 0, 0, 0, 0, 24, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, -8, 0;
    -6, -2, -2, 6, 0, 0, 22, -2, 0, 0, -2, -2, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8;
    -6, -2, 6, -2, 0, 0, -2, 22, 0, 0, -2, -2, 0, 0, 0, -8, 0, 0, 0, -8, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 24, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, -8, 0;
    0, 0, 0, 0, 0, -8, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0;
    -6, 6, -2, -2, 0, 0, -2, -2, 0, 0, 22, -2, -8, -8, 0, 0, 0, 0, 0, 0, 0, 0;
    18, -2, -2, -2, 0, 0, -2, -2, 0, 0, -2, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 24, 0, 0, -8, 0, 0, 0, 0;
    0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 24, 0, 0, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, -8, 0;
    0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0;
    0, 0, 0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 24, 0;
    0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32]

/-- Entrywise decidability for integer families indexed by two copies of `Fin n`.
  The pointwise `Decidable` instances are supplied explicitly: instance search cannot
  see through the `Matrix` type synonym when the two indices are bound. -/
private instance decidableForallEntriesZ {n : ℕ} (f : Matrix (Fin n) (Fin n) ℤ)
    (g : Fin n → Fin n → ℤ) : Decidable (∀ k l, f k l = g k l) :=
  @Nat.decidableForallFin n _ fun _ => @Nat.decidableForallFin n _ fun _ =>
    Int.instDecidableEq _ _

/-- The same, with both sides matrices. -/
private instance decidableForallEntriesZ' {n : ℕ} (f g : Matrix (Fin n) (Fin n) ℤ) :
    Decidable (∀ k l, f k l = g k l) :=
  @Nat.decidableForallFin n _ fun _ => @Nat.decidableForallFin n _ fun _ =>
    Int.instDecidableEq _ _

set_option maxRecDepth 40000 in
/-- The entries of the explicit boost-average matrix are the row-orbit sums of the
  integer weight-zero transitions. -/
lemma boostAverageOrbitZ_eq_sum : ∀ k l : Fin 22,
    boostAverageOrbitZ k l = ∑ d' ∈ rotationIndexSet (orbitRep k),
      ∑ i : Fin 3, weightZeroTransitionZ i d' (orbitRep l) := by
  decide +kernel

/-- The integer matrix casts to `48` times the row-orbit sums of the boost average. -/
lemma coe_boostAverageOrbitZ (k l : Fin 22) :
    ((boostAverageOrbitZ k l : ℤ) : ℚ)
      = 48 * ∑ d' ∈ rotationIndexSet (orbitRep k),
          boostAverageTransition d' (orbitRep l) := by
  simp only [boostAverageOrbitZ_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  calc ∑ i : Fin 3, ((weightZeroTransitionZ i d' (orbitRep l) : ℤ) : ℚ)
      = ∑ i : Fin 3, 16 * weightZeroTransition i d' (orbitRep l) :=
        Finset.sum_congr rfl fun i _ => coe_weightZeroTransitionZ i d' (orbitRep l)
    _ = 48 * boostAverageTransition d' (orbitRep l) := by
        simp only [boostAverageTransition, Matrix.of_apply]
        rw [← Finset.mul_sum]
        ring

include hT in
/-- One averaged round at orbit level, integer form: over the enumerated
  representatives, an averaged round acts by the integer matrix `boostAverageOrbitZ`
  with the overall `48⁻¹` normalisation. -/
lemma eq_sum_boostAverageOrbitZ_smul {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ k, ((48 : ℂ)⁻¹ * ∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
  have hcS_rep : ∀ k : Fin 22,
      (∑ k' : Fin 22, if orbitRep k' = orbitRep k then c k' else 0) = c k := by
    intro k
    simp [orbitRep_injective.eq_iff]
  have hxS : x = ∑ d ∈ rotationSubset,
      (∑ k' : Fin 22, if orbitRep k' = d then c k' else 0)
        • rotationOrbitSum (T := T) d := by
    calc x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k) := hx
      _ = ∑ k, (∑ k' : Fin 22, if orbitRep k' = orbitRep k then c k' else 0)
            • rotationOrbitSum (T := T) (orbitRep k) :=
          Finset.sum_congr rfl fun k _ => by rw [hcS_rep k]
      _ = _ := (sum_rotationSubset (fun d => (∑ k' : Fin 22,
            if orbitRep k' = d then c k' else 0) • rotationOrbitSum (T := T) d)).symm
  have hR := hT.eq_sum_boostAverageTransition_of_mem_rotationSubset _ hxS hw
  rw [hR, sum_rotationSubset]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [sum_rotationSubset (fun e => ((∑ d' ∈ rotationIndexSet (orbitRep k),
    boostAverageTransition d' e : ℚ) : ℂ)
      * ∑ k' : Fin 22, if orbitRep k' = e then c k' else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hcS_rep l]
  have hb := congrArg (fun q : ℚ => (q : ℂ)) (coe_boostAverageOrbitZ k l)
  push_cast at hb
  push_cast
  rw [hb]
  ring

include hT in
/-- Iterated averaged rounds at orbit level: `n` rounds act by the `n`-th power of
  the integer matrix with the `48⁻ⁿ` normalisation. -/
lemma eq_sum_pow_boostAverageOrbitZ_smul {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) (n : ℕ) :
    x = ∑ k, (((48 : ℂ) ^ n)⁻¹ * ∑ l, (((boostAverageOrbitZ ^ n) k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
  induction n with
  | zero =>
    rw [hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [pow_zero, pow_zero]
    simp [Matrix.one_apply, apply_ite (fun q : ℤ => (q : ℂ)), ite_mul, Finset.sum_ite_eq]
  | succ n ih =>
    rw [hT.eq_sum_boostAverageOrbitZ_smul
      (fun k => ((48 : ℂ) ^ n)⁻¹ * ∑ l, (((boostAverageOrbitZ ^ n) k l : ℤ) : ℂ) * c l)
      ih hw]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    calc (48 : ℂ)⁻¹ * ∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ)
          * (((48 : ℂ) ^ n)⁻¹ * ∑ m, (((boostAverageOrbitZ ^ n) l m : ℤ) : ℂ) * c m)
        = ((48 : ℂ) ^ (n + 1))⁻¹ * ∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ)
            * ∑ m, (((boostAverageOrbitZ ^ n) l m : ℤ) : ℂ) * c m := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [pow_succ]
          field_simp
      _ = ((48 : ℂ) ^ (n + 1))⁻¹ * ∑ m, (((boostAverageOrbitZ * boostAverageOrbitZ ^ n) k m
            : ℤ) : ℂ) * c m := by
          congr 1
          calc ∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ)
                * ∑ m, (((boostAverageOrbitZ ^ n) l m : ℤ) : ℂ) * c m
              = ∑ l, ∑ m, ((boostAverageOrbitZ k l : ℤ) : ℂ)
                  * ((((boostAverageOrbitZ ^ n) l m : ℤ) : ℂ) * c m) :=
                Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
            _ = ∑ m, (∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ)
                  * (((boostAverageOrbitZ ^ n) l m : ℤ) : ℂ)) * c m := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun m _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
            _ = ∑ m, (((boostAverageOrbitZ * boostAverageOrbitZ ^ n) k m : ℤ) : ℂ) * c m := by
                refine Finset.sum_congr rfl fun m _ => ?_
                congr 1
                rw [Matrix.mul_apply]
                push_cast
                rfl
      _ = ((48 : ℂ) ^ (n + 1))⁻¹
            * ∑ m, (((boostAverageOrbitZ ^ (n + 1)) k m : ℤ) : ℂ) * c m := by
          rw [← pow_succ' boostAverageOrbitZ n]

/-!

## H. The certificate polynomial and the contraction projector

On the orbit-sum span the boost average has rational spectrum, with eigenvalue `1`
exactly on the invariant contractions. The certificate polynomial
`λ(3λ-2)(3λ-1)(12λ²-11λ+1)` annihilates every other eigenvalue, so applied to the
iterated rounds it collapses them to the projector onto the invariant block.

-/

/-- Twenty-four times the projector onto the invariant block: the integer matrix
  `P` with `boostAverageOrbitZ * P = 48 • P` and `P * P = 24 • P`, so that `24⁻¹ • P`
  projects the orbit-sum span onto the eigenvalue-`48` block — the invariant
  contractions. -/
def contractionProjectorZ : Matrix (Fin 22) (Fin 22) ℤ :=
  !![3, -1, -1, -1, 0, 0, -1, -1, 0, 0, -1, 3, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1;
    -3, 5, -1, -1, 0, 0, -1, -1, 0, 0, 5, -3, -5, -5, 0, 1, 1, 0, 0, 1, 0, 1;
    -3, -1, 5, -1, 0, 0, -1, 5, 0, 0, -1, -3, 1, 1, 0, -5, 1, 0, 0, -5, 0, 1;
    -3, -1, -1, 5, 0, 0, 5, -1, 0, 0, -1, -3, 1, 1, 0, 1, -5, 0, 0, 1, 0, -5;
    0, 0, 0, 0, 3, -3, 0, 0, -3, 3, 0, 0, 0, 0, 3, 0, 0, -3, -3, 0, 3, 0;
    0, 0, 0, 0, -3, 3, 0, 0, 3, -3, 0, 0, 0, 0, -3, 0, 0, 3, 3, 0, -3, 0;
    -3, -1, -1, 5, 0, 0, 5, -1, 0, 0, -1, -3, 1, 1, 0, 1, -5, 0, 0, 1, 0, -5;
    -3, -1, 5, -1, 0, 0, -1, 5, 0, 0, -1, -3, 1, 1, 0, -5, 1, 0, 0, -5, 0, 1;
    0, 0, 0, 0, -3, 3, 0, 0, 3, -3, 0, 0, 0, 0, -3, 0, 0, 3, 3, 0, -3, 0;
    0, 0, 0, 0, 3, -3, 0, 0, -3, 3, 0, 0, 0, 0, 3, 0, 0, -3, -3, 0, 3, 0;
    -3, 5, -1, -1, 0, 0, -1, -1, 0, 0, 5, -3, -5, -5, 0, 1, 1, 0, 0, 1, 0, 1;
    9, -3, -3, -3, 0, 0, -3, -3, 0, 0, -3, 9, 3, 3, 0, 3, 3, 0, 0, 3, 0, 3;
    3, -5, 1, 1, 0, 0, 1, 1, 0, 0, -5, 3, 5, 5, 0, -1, -1, 0, 0, -1, 0, -1;
    3, -5, 1, 1, 0, 0, 1, 1, 0, 0, -5, 3, 5, 5, 0, -1, -1, 0, 0, -1, 0, -1;
    0, 0, 0, 0, 3, -3, 0, 0, -3, 3, 0, 0, 0, 0, 3, 0, 0, -3, -3, 0, 3, 0;
    3, 1, -5, 1, 0, 0, 1, -5, 0, 0, 1, 3, -1, -1, 0, 5, -1, 0, 0, 5, 0, -1;
    3, 1, 1, -5, 0, 0, -5, 1, 0, 0, 1, 3, -1, -1, 0, -1, 5, 0, 0, -1, 0, 5;
    0, 0, 0, 0, -3, 3, 0, 0, 3, -3, 0, 0, 0, 0, -3, 0, 0, 3, 3, 0, -3, 0;
    0, 0, 0, 0, -3, 3, 0, 0, 3, -3, 0, 0, 0, 0, -3, 0, 0, 3, 3, 0, -3, 0;
    3, 1, -5, 1, 0, 0, 1, -5, 0, 0, 1, 3, -1, -1, 0, 5, -1, 0, 0, 5, 0, -1;
    0, 0, 0, 0, 3, -3, 0, 0, -3, 3, 0, 0, 0, 0, 3, 0, 0, -3, -3, 0, 3, 0;
    3, 1, 1, -5, 0, 0, -5, 1, 0, 0, 1, 3, -1, -1, 0, -1, 5, 0, 0, -1, 0, 5]

/-- The certificate polynomial applied to the boost average: the integer-scaled
  annihilator of the non-invariant blocks, `μ(μ-32)(μ-16)(μ²-44μ+192)` at
  `μ = boostAverageOrbitZ` — the polynomial `λ(3λ-2)(3λ-1)(12λ²-11λ+1)` of the
  normalised average `λ = μ/48`, cleared of denominators. -/
def Q : Matrix (Fin 22) (Fin 22) ℤ :=
  boostAverageOrbitZ * (boostAverageOrbitZ - 32) * (boostAverageOrbitZ - 16) *
    (boostAverageOrbitZ * boostAverageOrbitZ - 44 • boostAverageOrbitZ + 192)

set_option maxRecDepth 40000 in
/-- The certificate collapses to the projector: applying the certificate polynomial
  to the boost average yields `393216` times `contractionProjectorZ`. Verified through
  materialised intermediate products, so each kernel step is a single multiplication of
  explicit integer matrices. -/
lemma Q_explicit : Q = (393216 : ℤ) • contractionProjectorZ := by
  have h1 : boostAverageOrbitZ * (boostAverageOrbitZ - 32)
      = (!![-72, -24, -24, -24, 0, 0, -24, -24, 0, 0, -24, 168, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        -72, -24, -24, -24, 0, 0, -24, -24, 0, 0, 232, -88, -224, -224, 0, 32, 32, 0, 0, 32, 0, 32;
        -72, -24, -24, -24, 0, 0, -24, 232, 0, 0, -24, -88, 32, 32, 0, -224, 32, 0, 0, -224, 0, 32;
        -72, -24, -24, -24, 0, 0, 232, -24, 0, 0, -24, -88, 32, 32, 0, 32, -224, 0, 0, 32, 0, -224;
        0, 0, 0, 0, 0, 0, 0, 0, -128, 128, 0, 0, 0, 0, 128, 0, 0, -128, -128, 0, 128, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 128, -128, 0, 0, 0, 0, -128, 0, 0, 128, 128, 0, -128, 0;
        -72, -24, -24, 232, 0, 0, -24, -24, 0, 0, -24, -88, 32, 32, 0, 32, -224, 0, 0, 32, 0, -224;
        -72, -24, 232, -24, 0, 0, -24, -24, 0, 0, -24, -88, 32, 32, 0, -224, 32, 0, 0, -224, 0, 32;
        0, 0, 0, 0, -128, 128, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 128, 128, 0, -128, 0;
        0, 0, 0, 0, 128, -128, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, -128, -128, 0, 128, 0;
        -72, 232, -24, -24, 0, 0, -24, -24, 0, 0, -24, -88, -224, -224, 0, 32, 32, 0, 0, 32, 0, 32;
        504, -88, -88, -88, 0, 0, -88, -88, 0, 0, -88, 360, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        96, -224, 32, 32, 0, 0, 32, 32, 0, 0, -224, 32, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        96, -224, 32, 32, 0, 0, 32, 32, 0, 0, -224, 32, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 128, -128, 0, 0, -128, 128, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 128, 0;
        96, 32, -224, 32, 0, 0, 32, -224, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0;
        96, 32, 32, -224, 0, 0, -224, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, 128;
        0, 0, 0, 0, -128, 128, 0, 0, 128, -128, 0, 0, 0, 0, -128, 0, 0, 0, 128, 0, 0, 0;
        0, 0, 0, 0, -128, 128, 0, 0, 128, -128, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, -128, 0;
        96, 32, -224, 32, 0, 0, 32, -224, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0;
        0, 0, 0, 0, 128, -128, 0, 0, -128, 128, 0, 0, 0, 0, 128, 0, 0, 0, -128, 0, 0, 0;
        96, 32, 32, -224, 0, 0, -224, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, 128] : Matrix (Fin 22) (Fin 22) ℤ) := by
    ext k l
    revert k l
    decide +kernel
  have h2 : (!![-72, -24, -24, -24, 0, 0, -24, -24, 0, 0, -24, 168, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        -72, -24, -24, -24, 0, 0, -24, -24, 0, 0, 232, -88, -224, -224, 0, 32, 32, 0, 0, 32, 0, 32;
        -72, -24, -24, -24, 0, 0, -24, 232, 0, 0, -24, -88, 32, 32, 0, -224, 32, 0, 0, -224, 0, 32;
        -72, -24, -24, -24, 0, 0, 232, -24, 0, 0, -24, -88, 32, 32, 0, 32, -224, 0, 0, 32, 0, -224;
        0, 0, 0, 0, 0, 0, 0, 0, -128, 128, 0, 0, 0, 0, 128, 0, 0, -128, -128, 0, 128, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 128, -128, 0, 0, 0, 0, -128, 0, 0, 128, 128, 0, -128, 0;
        -72, -24, -24, 232, 0, 0, -24, -24, 0, 0, -24, -88, 32, 32, 0, 32, -224, 0, 0, 32, 0, -224;
        -72, -24, 232, -24, 0, 0, -24, -24, 0, 0, -24, -88, 32, 32, 0, -224, 32, 0, 0, -224, 0, 32;
        0, 0, 0, 0, -128, 128, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 128, 128, 0, -128, 0;
        0, 0, 0, 0, 128, -128, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, -128, -128, 0, 128, 0;
        -72, 232, -24, -24, 0, 0, -24, -24, 0, 0, -24, -88, -224, -224, 0, 32, 32, 0, 0, 32, 0, 32;
        504, -88, -88, -88, 0, 0, -88, -88, 0, 0, -88, 360, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        96, -224, 32, 32, 0, 0, 32, 32, 0, 0, -224, 32, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        96, -224, 32, 32, 0, 0, 32, 32, 0, 0, -224, 32, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 128, -128, 0, 0, -128, 128, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 128, 0;
        96, 32, -224, 32, 0, 0, 32, -224, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0;
        96, 32, 32, -224, 0, 0, -224, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, 128;
        0, 0, 0, 0, -128, 128, 0, 0, 128, -128, 0, 0, 0, 0, -128, 0, 0, 0, 128, 0, 0, 0;
        0, 0, 0, 0, -128, 128, 0, 0, 128, -128, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, -128, 0;
        96, 32, -224, 32, 0, 0, 32, -224, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0;
        0, 0, 0, 0, 128, -128, 0, 0, -128, 128, 0, 0, 0, 0, 128, 0, 0, 0, -128, 0, 0, 0;
        96, 32, 32, -224, 0, 0, -224, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, 128] : Matrix (Fin 22) (Fin 22) ℤ)
        * (boostAverageOrbitZ - 16)
      = (!![3744, -800, -800, -800, 0, 0, -800, -800, 0, 0, -800, 3552, 896, 896, 0, 896, 896, 0, 0, 896, 0, 896;
        -2400, 5344, -800, -800, 0, 0, -800, -800, 0, 0, 5344, -2592, -5248, -5248, 0, 896, 896, 0, 0, 896, 0, 896;
        -2400, -800, 5344, -800, 0, 0, -800, 5344, 0, 0, -800, -2592, 896, 896, 0, -5248, 896, 0, 0, -5248, 0, 896;
        -2400, -800, -800, 5344, 0, 0, 5344, -800, 0, 0, -800, -2592, 896, 896, 0, 896, -5248, 0, 0, 896, 0, -5248;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        -2400, -800, -800, 5344, 0, 0, 5344, -800, 0, 0, -800, -2592, 896, 896, 0, 896, -5248, 0, 0, 896, 0, -5248;
        -2400, -800, 5344, -800, 0, 0, -800, 5344, 0, 0, -800, -2592, 896, 896, 0, -5248, 896, 0, 0, -5248, 0, 896;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        -2400, 5344, -800, -800, 0, 0, -800, -800, 0, 0, 5344, -2592, -5248, -5248, 0, 896, 896, 0, 0, 896, 0, 896;
        10656, -2592, -2592, -2592, 0, 0, -2592, -2592, 0, 0, -2592, 12000, 1920, 1920, 0, 1920, 1920, 0, 0, 1920, 0, 1920;
        2688, -5248, 896, 896, 0, 0, 896, 896, 0, 0, -5248, 1920, 5632, 5632, 0, -512, -512, 0, 0, -512, 0, -512;
        2688, -5248, 896, 896, 0, 0, 896, 896, 0, 0, -5248, 1920, 5632, 5632, 0, -512, -512, 0, 0, -512, 0, -512;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        2688, 896, -5248, 896, 0, 0, 896, -5248, 0, 0, 896, 1920, -512, -512, 0, 5632, -512, 0, 0, 5632, 0, -512;
        2688, 896, 896, -5248, 0, 0, -5248, 896, 0, 0, 896, 1920, -512, -512, 0, -512, 5632, 0, 0, -512, 0, 5632;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        2688, 896, -5248, 896, 0, 0, 896, -5248, 0, 0, 896, 1920, -512, -512, 0, 5632, -512, 0, 0, 5632, 0, -512;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        2688, 896, 896, -5248, 0, 0, -5248, 896, 0, 0, 896, 1920, -512, -512, 0, -512, 5632, 0, 0, -512, 0, 5632] : Matrix (Fin 22) (Fin 22) ℤ) := by
    ext k l
    revert k l
    decide +kernel
  have h3 : boostAverageOrbitZ * boostAverageOrbitZ - 44 • boostAverageOrbitZ + 192
      = (!![-96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        0, -96, 0, 0, 0, 0, 0, 0, 0, 0, 160, -64, -128, -128, 0, 32, 32, 0, 0, 32, 0, 32;
        0, 0, -96, 0, 0, 0, 0, 160, 0, 0, 0, -64, 32, 32, 0, -128, 32, 0, 0, -128, 0, 32;
        0, 0, 0, -96, 0, 0, 160, 0, 0, 0, 0, -64, 32, 32, 0, 32, -128, 0, 0, 32, 0, -128;
        0, 0, 0, 0, -96, 0, 0, 0, -32, 128, 0, 0, 0, 0, 128, 0, 0, -32, -32, 0, 128, 0;
        0, 0, 0, 0, 0, -96, 0, 0, 128, -32, 0, 0, 0, 0, -32, 0, 0, 128, 128, 0, -32, 0;
        0, 0, 0, 160, 0, 0, -96, 0, 0, 0, 0, -64, 32, 32, 0, 32, -128, 0, 0, 32, 0, -128;
        0, 0, 160, 0, 0, 0, 0, -96, 0, 0, 0, -64, 32, 32, 0, -128, 32, 0, 0, -128, 0, 32;
        0, 0, 0, 0, -32, 128, 0, 0, -96, 0, 0, 0, 0, 0, -32, 0, 0, 128, 128, 0, -32, 0;
        0, 0, 0, 0, 128, -32, 0, 0, 0, -96, 0, 0, 0, 0, 128, 0, 0, -32, -32, 0, 128, 0;
        0, 160, 0, 0, 0, 0, 0, 0, 0, 0, -96, -64, -128, -128, 0, 32, 32, 0, 0, 32, 0, 32;
        288, -64, -64, -64, 0, 0, -64, -64, 0, 0, -64, 96, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        96, -128, 32, 32, 0, 0, 32, 32, 0, 0, -128, 32, -64, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        96, -128, 32, 32, 0, 0, 32, 32, 0, 0, -128, 32, 128, -64, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 128, -32, 0, 0, -32, 128, 0, 0, 0, 0, -96, 0, 0, -32, 0, 0, 128, 0;
        96, 32, -128, 32, 0, 0, 32, -128, 0, 0, 32, 32, 0, 0, 0, -64, 0, 0, 0, 128, 0, 0;
        96, 32, 32, -128, 0, 0, -128, 32, 0, 0, 32, 32, 0, 0, 0, 0, -64, 0, 0, 0, 0, 128;
        0, 0, 0, 0, -32, 128, 0, 0, 128, -32, 0, 0, 0, 0, -32, 0, 0, -96, 128, 0, 0, 0;
        0, 0, 0, 0, -32, 128, 0, 0, 128, -32, 0, 0, 0, 0, 0, 0, 0, 128, -96, 0, -32, 0;
        96, 32, -128, 32, 0, 0, 32, -128, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, -64, 0, 0;
        0, 0, 0, 0, 128, -32, 0, 0, -32, 128, 0, 0, 0, 0, 128, 0, 0, 0, -32, 0, -96, 0;
        96, 32, 32, -128, 0, 0, -128, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, -64] : Matrix (Fin 22) (Fin 22) ℤ) := by
    ext k l
    revert k l
    decide +kernel
  have h4 : (!![3744, -800, -800, -800, 0, 0, -800, -800, 0, 0, -800, 3552, 896, 896, 0, 896, 896, 0, 0, 896, 0, 896;
        -2400, 5344, -800, -800, 0, 0, -800, -800, 0, 0, 5344, -2592, -5248, -5248, 0, 896, 896, 0, 0, 896, 0, 896;
        -2400, -800, 5344, -800, 0, 0, -800, 5344, 0, 0, -800, -2592, 896, 896, 0, -5248, 896, 0, 0, -5248, 0, 896;
        -2400, -800, -800, 5344, 0, 0, 5344, -800, 0, 0, -800, -2592, 896, 896, 0, 896, -5248, 0, 0, 896, 0, -5248;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        -2400, -800, -800, 5344, 0, 0, 5344, -800, 0, 0, -800, -2592, 896, 896, 0, 896, -5248, 0, 0, 896, 0, -5248;
        -2400, -800, 5344, -800, 0, 0, -800, 5344, 0, 0, -800, -2592, 896, 896, 0, -5248, 896, 0, 0, -5248, 0, 896;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        -2400, 5344, -800, -800, 0, 0, -800, -800, 0, 0, 5344, -2592, -5248, -5248, 0, 896, 896, 0, 0, 896, 0, 896;
        10656, -2592, -2592, -2592, 0, 0, -2592, -2592, 0, 0, -2592, 12000, 1920, 1920, 0, 1920, 1920, 0, 0, 1920, 0, 1920;
        2688, -5248, 896, 896, 0, 0, 896, 896, 0, 0, -5248, 1920, 5632, 5632, 0, -512, -512, 0, 0, -512, 0, -512;
        2688, -5248, 896, 896, 0, 0, 896, 896, 0, 0, -5248, 1920, 5632, 5632, 0, -512, -512, 0, 0, -512, 0, -512;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        2688, 896, -5248, 896, 0, 0, 896, -5248, 0, 0, 896, 1920, -512, -512, 0, 5632, -512, 0, 0, 5632, 0, -512;
        2688, 896, 896, -5248, 0, 0, -5248, 896, 0, 0, 896, 1920, -512, -512, 0, -512, 5632, 0, 0, -512, 0, 5632;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        0, 0, 0, 0, -3072, 3072, 0, 0, 3072, -3072, 0, 0, 0, 0, -3072, 0, 0, 3072, 3072, 0, -3072, 0;
        2688, 896, -5248, 896, 0, 0, 896, -5248, 0, 0, 896, 1920, -512, -512, 0, 5632, -512, 0, 0, 5632, 0, -512;
        0, 0, 0, 0, 3072, -3072, 0, 0, -3072, 3072, 0, 0, 0, 0, 3072, 0, 0, -3072, -3072, 0, 3072, 0;
        2688, 896, 896, -5248, 0, 0, -5248, 896, 0, 0, 896, 1920, -512, -512, 0, -512, 5632, 0, 0, -512, 0, 5632] : Matrix (Fin 22) (Fin 22) ℤ)
        * (!![-96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        0, -96, 0, 0, 0, 0, 0, 0, 0, 0, 160, -64, -128, -128, 0, 32, 32, 0, 0, 32, 0, 32;
        0, 0, -96, 0, 0, 0, 0, 160, 0, 0, 0, -64, 32, 32, 0, -128, 32, 0, 0, -128, 0, 32;
        0, 0, 0, -96, 0, 0, 160, 0, 0, 0, 0, -64, 32, 32, 0, 32, -128, 0, 0, 32, 0, -128;
        0, 0, 0, 0, -96, 0, 0, 0, -32, 128, 0, 0, 0, 0, 128, 0, 0, -32, -32, 0, 128, 0;
        0, 0, 0, 0, 0, -96, 0, 0, 128, -32, 0, 0, 0, 0, -32, 0, 0, 128, 128, 0, -32, 0;
        0, 0, 0, 160, 0, 0, -96, 0, 0, 0, 0, -64, 32, 32, 0, 32, -128, 0, 0, 32, 0, -128;
        0, 0, 160, 0, 0, 0, 0, -96, 0, 0, 0, -64, 32, 32, 0, -128, 32, 0, 0, -128, 0, 32;
        0, 0, 0, 0, -32, 128, 0, 0, -96, 0, 0, 0, 0, 0, -32, 0, 0, 128, 128, 0, -32, 0;
        0, 0, 0, 0, 128, -32, 0, 0, 0, -96, 0, 0, 0, 0, 128, 0, 0, -32, -32, 0, 128, 0;
        0, 160, 0, 0, 0, 0, 0, 0, 0, 0, -96, -64, -128, -128, 0, 32, 32, 0, 0, 32, 0, 32;
        288, -64, -64, -64, 0, 0, -64, -64, 0, 0, -64, 96, 32, 32, 0, 32, 32, 0, 0, 32, 0, 32;
        96, -128, 32, 32, 0, 0, 32, 32, 0, 0, -128, 32, -64, 128, 0, 0, 0, 0, 0, 0, 0, 0;
        96, -128, 32, 32, 0, 0, 32, 32, 0, 0, -128, 32, 128, -64, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 128, -32, 0, 0, -32, 128, 0, 0, 0, 0, -96, 0, 0, -32, 0, 0, 128, 0;
        96, 32, -128, 32, 0, 0, 32, -128, 0, 0, 32, 32, 0, 0, 0, -64, 0, 0, 0, 128, 0, 0;
        96, 32, 32, -128, 0, 0, -128, 32, 0, 0, 32, 32, 0, 0, 0, 0, -64, 0, 0, 0, 0, 128;
        0, 0, 0, 0, -32, 128, 0, 0, 128, -32, 0, 0, 0, 0, -32, 0, 0, -96, 128, 0, 0, 0;
        0, 0, 0, 0, -32, 128, 0, 0, 128, -32, 0, 0, 0, 0, 0, 0, 0, 128, -96, 0, -32, 0;
        96, 32, -128, 32, 0, 0, 32, -128, 0, 0, 32, 32, 0, 0, 0, 128, 0, 0, 0, -64, 0, 0;
        0, 0, 0, 0, 128, -32, 0, 0, -32, 128, 0, 0, 0, 0, 128, 0, 0, 0, -32, 0, -96, 0;
        96, 32, 32, -128, 0, 0, -128, 32, 0, 0, 32, 32, 0, 0, 0, 0, 128, 0, 0, 0, 0, -64] : Matrix (Fin 22) (Fin 22) ℤ)
      = (393216 : ℤ) • contractionProjectorZ := by
    ext k l
    revert k l
    decide +kernel
  rw [Q, h1, h2, h3, h4]

/-- The certificate polynomial expanded into powers. -/
lemma Q_eq_poly : Q = boostAverageOrbitZ ^ 5 - (92 : ℤ) • boostAverageOrbitZ ^ 4
    + (2816 : ℤ) • boostAverageOrbitZ ^ 3 - (31744 : ℤ) • boostAverageOrbitZ ^ 2
    + (98304 : ℤ) • boostAverageOrbitZ := by
  rw [Q]
  noncomm_ring

include hT in
/-- The certificate round: applying the certificate polynomial of the averaged round
  to the coefficients reproduces `x` — the combination of five iterated rounds weighted
  by the certificate coefficients. -/
lemma eq_sum_Q_smul {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ k, ((9437184 : ℂ)⁻¹ * ∑ l, ((Q k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
  have h1 := hT.eq_sum_pow_boostAverageOrbitZ_smul c hx hw 1
  have h2 := hT.eq_sum_pow_boostAverageOrbitZ_smul c hx hw 2
  have h3 := hT.eq_sum_pow_boostAverageOrbitZ_smul c hx hw 3
  have h4 := hT.eq_sum_pow_boostAverageOrbitZ_smul c hx hw 4
  have h5 := hT.eq_sum_pow_boostAverageOrbitZ_smul c hx hw 5
  have key : (27 : ℂ) • x - (207 / 4 : ℂ) • x + (33 : ℂ) • x - (31 / 4 : ℂ) • x
      + (2⁻¹ : ℂ) • x
      = ∑ k, ((9437184 : ℂ)⁻¹ * ∑ l, ((Q k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
    nth_rewrite 1 [h5]
    nth_rewrite 1 [h4]
    nth_rewrite 1 [h3]
    nth_rewrite 1 [h2]
    nth_rewrite 1 [h1]
    simp only [Finset.smul_sum, smul_smul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← sub_smul, ← add_smul]
    congr 1
    have hQc : ∀ l, ((Q k l : ℤ) : ℂ)
        = (((boostAverageOrbitZ ^ 5) k l : ℤ) : ℂ)
          - 92 * (((boostAverageOrbitZ ^ 4) k l : ℤ) : ℂ)
          + 2816 * (((boostAverageOrbitZ ^ 3) k l : ℤ) : ℂ)
          - 31744 * (((boostAverageOrbitZ ^ 2) k l : ℤ) : ℂ)
          + 98304 * ((boostAverageOrbitZ k l : ℤ) : ℂ) := fun l => by
      rw [Q_eq_poly]
      push_cast [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hsplit : ∑ l, ((Q k l : ℤ) : ℂ) * c l
        = (∑ l, (((boostAverageOrbitZ ^ 5) k l : ℤ) : ℂ) * c l)
          - 92 * (∑ l, (((boostAverageOrbitZ ^ 4) k l : ℤ) : ℂ) * c l)
          + 2816 * (∑ l, (((boostAverageOrbitZ ^ 3) k l : ℤ) : ℂ) * c l)
          - 31744 * (∑ l, (((boostAverageOrbitZ ^ 2) k l : ℤ) : ℂ) * c l)
          + 98304 * (∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ) * c l) := by
      simp only [hQc, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hsplit]
    field_simp
    ring_nf
  calc x = (27 : ℂ) • x - (207 / 4 : ℂ) • x + (33 : ℂ) • x - (31 / 4 : ℂ) • x
        + (2⁻¹ : ℂ) • x := by module
    _ = _ := key

include hT in
/-- The projector round: the certificate collapses to `24⁻¹` times the integer
  projector matrix — one clean application of `contractionProjectorZ` reproduces the
  coefficients of any all-axes weight-zero element. -/
lemma eq_sum_contractionProjectorZ_smul {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ k, ((24 : ℂ)⁻¹ * ∑ l, ((contractionProjectorZ k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
  rw [hT.eq_sum_Q_smul c hx hw]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hP : ∀ l, ((Q k l : ℤ) : ℂ) = 393216 * ((contractionProjectorZ k l : ℤ) : ℂ) :=
    fun l => by
      rw [Q_explicit]
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
  simp only [hP, mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  ring

/-!

## I. The four invariant contractions

## I.1. The metric and Levi-Civita contractions

The three double metric contractions — outer `g^{μν} g^{ρσ} T_{μνρσ}`, inner
`g^{μρ} g^{νσ} T_{μνρσ}`, split `g^{μσ} g^{νρ} T_{μνρσ}` — and the Levi-Civita
contraction `ε^{μνρσ} T_{μνρσ}`.

-/

/-- The Minkowski sign of a direction: `+1` on time, `-1` on space. -/
def minkowskiSignZ : Fin 1 ⊕ Fin 3 → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- The Minkowski metric on direction letters. -/
def etaZ (μ ν : Fin 1 ⊕ Fin 3) : ℤ := if μ = ν then minkowskiSignZ μ else 0

/-- The numeric label of a direction, for the Levi-Civita sign. -/
def dirNum : Fin 1 ⊕ Fin 3 → ℤ := Sum.elim (fun _ => 0) (fun j => (j : ℤ) + 1)

/-- The Levi-Civita sign of a four-tuple of directions: the product of the signs of the
  label differences — `±1` on the permutations of `(t, x, y, z)` and `0` otherwise. -/
def epsilonSignZ (d : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  (dirNum (d 1) - dirNum (d 0)).sign * (dirNum (d 2) - dirNum (d 0)).sign
    * (dirNum (d 3) - dirNum (d 0)).sign * (dirNum (d 2) - dirNum (d 1)).sign
    * (dirNum (d 3) - dirNum (d 1)).sign * (dirNum (d 3) - dirNum (d 2)).sign

/-- The outer contraction `g^{μν} g^{ρσ} T_{μνρσ}`. -/
noncomputable def outerContraction : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 1) * etaZ (d 2) (d 3) : ℤ) : ℂ) • T d

/-- The inner contraction `g^{μρ} g^{νσ} T_{μνρσ}`. -/
noncomputable def innerContraction : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 2) * etaZ (d 1) (d 3) : ℤ) : ℂ) • T d

/-- The split contraction `g^{μσ} g^{νρ} T_{μνρσ}`. -/
noncomputable def splitContraction : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 3) * etaZ (d 1) (d 2) : ℤ) : ℂ) • T d

/-- The Levi-Civita contraction `ε^{μνρσ} T_{μνρσ}`. -/
noncomputable def epsilonContraction : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : ℂ) • T d

include hT in
/-- The outer contraction lies in the span of the components. -/
lemma outerContraction_mem_span : outerContraction (T := T) ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

include hT in
/-- The inner contraction lies in the span of the components. -/
lemma innerContraction_mem_span : innerContraction (T := T) ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

include hT in
/-- The split contraction lies in the span of the components. -/
lemma splitContraction_mem_span : splitContraction (T := T) ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

include hT in
/-- The Levi-Civita contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span : epsilonContraction (T := T) ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## I.2. Orbit coordinates and the projector factorisation

Integer orbit vectors and weight rows for each contraction; three times the projector
is the sum of their four rank-one products.

-/

/-- The outer contraction in orbit coordinates (times three). -/
def outerOrbitZ : Fin 22 → ℤ := ![1, -3, 0, 0, 0, 0, 0, 0, 0, 0, -3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The inner contraction in orbit coordinates (times three). -/
def innerOrbitZ : Fin 22 → ℤ := ![1, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0]

/-- The split contraction in orbit coordinates (times three). -/
def splitOrbitZ : Fin 22 → ℤ := ![1, 0, 0, -3, 0, 0, -3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3]

/-- The Levi-Civita contraction in orbit coordinates. -/
def epsilonOrbitZ : Fin 22 → ℤ := ![0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 1, 0]

/-- The outer weight row of the projector factorisation. -/
def outerWeightZ : Fin 22 → ℤ :=
  ![3, -5, 1, 1, 0, 0, 1, 1, 0, 0, -5, 3, 5, 5, 0, -1, -1, 0, 0, -1, 0, -1]

/-- The inner weight row of the projector factorisation. -/
def innerWeightZ : Fin 22 → ℤ :=
  ![3, 1, -5, 1, 0, 0, 1, -5, 0, 0, 1, 3, -1, -1, 0, 5, -1, 0, 0, 5, 0, -1]

/-- The split weight row of the projector factorisation. -/
def splitWeightZ : Fin 22 → ℤ :=
  ![3, 1, 1, -5, 0, 0, -5, 1, 0, 0, 1, 3, -1, -1, 0, -1, 5, 0, 0, -1, 0, 5]

/-- The Levi-Civita weight row of the projector factorisation. -/
def epsilonWeightZ : Fin 22 → ℤ :=
  ![0, 0, 0, 0, 9, -9, 0, 0, -9, 9, 0, 0, 0, 0, 9, 0, 0, -9, -9, 0, 9, 0]

/-- The projector factors through the four invariants: three times the projector is
  the sum of the four rank-one products of an invariant orbit vector with its weight
  row. -/
lemma three_mul_contractionProjectorZ : ∀ k l : Fin 22,
    3 * contractionProjectorZ k l
      = outerOrbitZ k * outerWeightZ l + innerOrbitZ k * innerWeightZ l
        + splitOrbitZ k * splitWeightZ l + epsilonOrbitZ k * epsilonWeightZ l := by
  decide +kernel

/-!

## I.3. The orbit vectors represent the contractions

-/

/-- The orbit sum expanded through the orbit multiplicity. -/
lemma rotationOrbitSum_eq_sum (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitSum (T := T) d
      = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3, ((rotationOrbitCoeff d e : ℤ) : ℂ) • T e := by
  rw [rotationOrbitSum]
  simp [rotationOrbitCoeff, apply_ite (fun n : ℤ => (n : ℂ)), add_smul, ite_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- A combination of the representative orbit sums, expanded into the generators. -/
lemma sum_smul_rotationOrbitSum_orbitRep (c : Fin 22 → ℂ) :
    ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k)
      = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (∑ k, c k * ((rotationOrbitCoeff (orbitRep k) e : ℤ) : ℂ)) • T e := by
  calc ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k)
      = ∑ k, ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (c k * ((rotationOrbitCoeff (orbitRep k) e : ℤ) : ℂ)) • T e := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rotationOrbitSum_eq_sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun e _ => smul_smul _ _ _
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => (Finset.sum_smul).symm

/-- The outer orbit vector against the orbit multiplicities gives the outer metric
  coefficients. -/
lemma sum_outerOrbitZ_mul_rotationOrbitCoeff : ∀ e : Fin 4 → Fin 1 ⊕ Fin 3,
    (∑ k, outerOrbitZ k * rotationOrbitCoeff (orbitRep k) e)
      = 3 * (etaZ (e 0) (e 1) * etaZ (e 2) (e 3)) := by
  decide +kernel

/-- The inner orbit vector against the orbit multiplicities gives the inner metric
  coefficients. -/
lemma sum_innerOrbitZ_mul_rotationOrbitCoeff : ∀ e : Fin 4 → Fin 1 ⊕ Fin 3,
    (∑ k, innerOrbitZ k * rotationOrbitCoeff (orbitRep k) e)
      = 3 * (etaZ (e 0) (e 2) * etaZ (e 1) (e 3)) := by
  decide +kernel

/-- The split orbit vector against the orbit multiplicities gives the split metric
  coefficients. -/
lemma sum_splitOrbitZ_mul_rotationOrbitCoeff : ∀ e : Fin 4 → Fin 1 ⊕ Fin 3,
    (∑ k, splitOrbitZ k * rotationOrbitCoeff (orbitRep k) e)
      = 3 * (etaZ (e 0) (e 3) * etaZ (e 1) (e 2)) := by
  decide +kernel

/-- The Levi-Civita orbit vector against the orbit multiplicities gives the Levi-Civita
  signs. -/
lemma sum_epsilonOrbitZ_mul_rotationOrbitCoeff : ∀ e : Fin 4 → Fin 1 ⊕ Fin 3,
    (∑ k, epsilonOrbitZ k * rotationOrbitCoeff (orbitRep k) e) = epsilonSignZ e := by
  decide +kernel

/-- The outer orbit vector represents three times the outer contraction. -/
lemma sum_outerOrbitZ_smul_rotationOrbitSum :
    ∑ k, ((outerOrbitZ k : ℤ) : ℂ) • rotationOrbitSum (T := T) (orbitRep k)
      = (3 : ℂ) • outerContraction (T := T) := by
  rw [sum_smul_rotationOrbitSum_orbitRep, outerContraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_smul]
  congr 1
  exact_mod_cast sum_outerOrbitZ_mul_rotationOrbitCoeff e

/-- The inner orbit vector represents three times the inner contraction. -/
lemma sum_innerOrbitZ_smul_rotationOrbitSum :
    ∑ k, ((innerOrbitZ k : ℤ) : ℂ) • rotationOrbitSum (T := T) (orbitRep k)
      = (3 : ℂ) • innerContraction (T := T) := by
  rw [sum_smul_rotationOrbitSum_orbitRep, innerContraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_smul]
  congr 1
  exact_mod_cast sum_innerOrbitZ_mul_rotationOrbitCoeff e

/-- The split orbit vector represents three times the split contraction. -/
lemma sum_splitOrbitZ_smul_rotationOrbitSum :
    ∑ k, ((splitOrbitZ k : ℤ) : ℂ) • rotationOrbitSum (T := T) (orbitRep k)
      = (3 : ℂ) • splitContraction (T := T) := by
  rw [sum_smul_rotationOrbitSum_orbitRep, splitContraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_smul]
  congr 1
  exact_mod_cast sum_splitOrbitZ_mul_rotationOrbitCoeff e

/-- The Levi-Civita orbit vector represents the Levi-Civita contraction. -/
lemma sum_epsilonOrbitZ_smul_rotationOrbitSum :
    ∑ k, ((epsilonOrbitZ k : ℤ) : ℂ) • rotationOrbitSum (T := T) (orbitRep k)
      = epsilonContraction (T := T) := by
  rw [sum_smul_rotationOrbitSum_orbitRep, epsilonContraction]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  exact_mod_cast sum_epsilonOrbitZ_mul_rotationOrbitCoeff e

/-!

## I.4. The projector round lands in the contractions

-/

include hT in
/-- Boost-invariant orbit combinations are spanned by the four contractions: an
  all-axes weight-zero combination of the representative orbit sums is a linear
  combination of the outer, inner and split metric contractions and the Levi-Civita
  contraction. -/
theorem exists_smul_contraction_of_eq_sum_orbitRep {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    ∃ a₁ a₂ a₃ a₄ : ℂ,
      x = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) := by
  refine ⟨(24 : ℂ)⁻¹ * ∑ l, ((outerWeightZ l : ℤ) : ℂ) * c l,
    (24 : ℂ)⁻¹ * ∑ l, ((innerWeightZ l : ℤ) : ℂ) * c l,
    (24 : ℂ)⁻¹ * ∑ l, ((splitWeightZ l : ℤ) : ℂ) * c l,
    (72 : ℂ)⁻¹ * ∑ l, ((epsilonWeightZ l : ℤ) : ℂ) * c l, ?_⟩
  rw [hT.eq_sum_contractionProjectorZ_smul c hx hw]
  have hfac : ∀ k, (24 : ℂ)⁻¹ * ∑ l, ((contractionProjectorZ k l : ℤ) : ℂ) * c l
      = ((outerOrbitZ k : ℤ) : ℂ) * ((72 : ℂ)⁻¹ * ∑ l, ((outerWeightZ l : ℤ) : ℂ) * c l)
        + ((innerOrbitZ k : ℤ) : ℂ) * ((72 : ℂ)⁻¹ * ∑ l, ((innerWeightZ l : ℤ) : ℂ) * c l)
        + ((splitOrbitZ k : ℤ) : ℂ) * ((72 : ℂ)⁻¹ * ∑ l, ((splitWeightZ l : ℤ) : ℂ) * c l)
        + ((epsilonOrbitZ k : ℤ) : ℂ)
            * ((72 : ℂ)⁻¹ * ∑ l, ((epsilonWeightZ l : ℤ) : ℂ) * c l) := by
    intro k
    have hZ : ∀ l, ((contractionProjectorZ k l : ℤ) : ℂ)
        = (3 : ℂ)⁻¹ * (((outerOrbitZ k : ℤ) : ℂ) * ((outerWeightZ l : ℤ) : ℂ)
          + ((innerOrbitZ k : ℤ) : ℂ) * ((innerWeightZ l : ℤ) : ℂ)
          + ((splitOrbitZ k : ℤ) : ℂ) * ((splitWeightZ l : ℤ) : ℂ)
          + ((epsilonOrbitZ k : ℤ) : ℂ) * ((epsilonWeightZ l : ℤ) : ℂ)) := by
      intro l
      have h := three_mul_contractionProjectorZ k l
      have h' := congrArg (fun n : ℤ => ((n : ℤ) : ℂ)) h
      push_cast at h'
      field_simp
      linear_combination h'
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ l]
    field_simp
    ring
  simp only [hfac, add_smul, Finset.sum_add_distrib]
  have hpull : ∀ (v : Fin 22 → ℤ) (α : ℂ),
      (∑ k, (((v k : ℤ) : ℂ) * α) • rotationOrbitSum (T := T) (orbitRep k))
        = α • ∑ k, ((v k : ℤ) : ℂ) • rotationOrbitSum (T := T) (orbitRep k) := by
    intro v α
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  rw [hpull outerOrbitZ _, hpull innerOrbitZ _, hpull splitOrbitZ _, hpull epsilonOrbitZ _,
    sum_outerOrbitZ_smul_rotationOrbitSum, sum_innerOrbitZ_smul_rotationOrbitSum,
    sum_splitOrbitZ_smul_rotationOrbitSum, sum_epsilonOrbitZ_smul_rotationOrbitSum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · rw [smul_smul]
    congr 1
    field_simp
    ring
  · rw [smul_smul]
    congr 1
    field_simp
    ring
  · rw [smul_smul]
    congr 1
    field_simp
    ring
  · rfl
/-!

## I.5. The metric and the Levi-Civita sign under a Lorentz transformation

The four contractions are built from two integer symbols, the metric `etaZ` and the
Levi-Civita sign `epsilonSignZ`, and the invariance of the contractions is the
invariance of those symbols. For the metric that is the defining property
`Λ η Λᵀ = η` of the Lorentz group, read entrywise. For the Levi-Civita sign it is the
transformation law of a determinant, `∑_d ε d ∏ᵢ Λ (a i) (d i) = det Λ * ε a`, which
holds because `ε` is the determinant of the Kronecker matrix of a multi-index against
the standard listing of the four directions; the sign is then invariant for the proper
transformations, and those coming from `SL(2,ℂ)` are proper.

-/

/-- A sum over families of four four-vector indices is a fourfold sum. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3, F ![x, y, z, w] := by
  rw [show (∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
      Fintype.sum_equiv
        { toFun := fun d => (d 0, d 1, d 2, d 3)
          invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
          left_inv := fun d => by funext i; fin_cases i <;> simp
          right_inv := fun p => by simp } _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-- The integer metric is the Minkowski matrix. -/
lemma etaZ_cast (μ ν : Fin 1 ⊕ Fin 3) : ((etaZ μ ν : ℤ) : ℝ) = minkowskiMatrix μ ν := by
  rcases eq_or_ne μ ν with rfl | h
  · match μ with
    | Sum.inl i => fin_cases i; simp [etaZ, minkowskiSignZ]
    | Sum.inr i => simp [etaZ, minkowskiSignZ]
  · simp [etaZ, h]

/-- The metric is carried to itself by a Lorentz matrix: this is `Λ η Λᵀ = η`, the
  defining property of the Lorentz group, read on the entry `(a, b)`. -/
lemma sum_etaZ_mul (Λ : LorentzGroup 3) (a b : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ((etaZ x y : ℤ) : ℂ)
        * (((Λ.1 a x : ℝ) : ℂ) * ((Λ.1 b y : ℝ) : ℂ))
      = ((etaZ a b : ℤ) : ℂ) := by
  have hR : ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3,
      ((etaZ x y : ℤ) : ℝ) * (Λ.1 a x * Λ.1 b y) = ((etaZ a b : ℤ) : ℝ) := by
    have h := congrFun (congrFun
      (LorentzGroup.mul_minkowskiMatrix_mul_transpose (Λ := Λ)) a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [etaZ_cast, ← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [etaZ_cast]; ring
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  push_cast at hC ⊢
  exact hC

/-- The outer pairing of two metrics is carried to itself by a Lorentz matrix: the
  fourfold sum factors into two copies of `sum_etaZ_mul`. -/
lemma sum_outerPair_mul (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 1) * etaZ (d 2) (d 3) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = ((etaZ (a 0) (a 1) * etaZ (a 2) (a 3) : ℤ) : ℂ) := by
  have key : ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 1) * etaZ (d 2) (d 3) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = (∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ((etaZ x y : ℤ) : ℂ)
            * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 1) y : ℝ) : ℂ)))
        * (∑ z : Fin 1 ⊕ Fin 3, ∑ w : Fin 1 ⊕ Fin 3, ((etaZ z w : ℤ) : ℂ)
            * (((Λ.1 (a 2) z : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
    rw [sum_pi_four]
    have hterm : ∀ x y z w : Fin 1 ⊕ Fin 3,
        ((etaZ (![x, y, z, w] 0) (![x, y, z, w] 1)
            * etaZ (![x, y, z, w] 2) (![x, y, z, w] 3) : ℤ) : ℂ)
          * ∏ i, ((Λ.1 (a i) (![x, y, z, w] i) : ℝ) : ℂ)
        = (((etaZ x y : ℤ) : ℂ) * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 1) y : ℝ) : ℂ)))
          * (((etaZ z w : ℤ) : ℂ)
            * (((Λ.1 (a 2) z : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
      intro x y z w
      simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      push_cast
      ring
    simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [key, sum_etaZ_mul, sum_etaZ_mul]
  push_cast
  ring

/-- The inner pairing of two metrics is carried to itself by a Lorentz matrix, by the
  same factorisation with the indices interleaved. -/
lemma sum_innerPair_mul (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 2) * etaZ (d 1) (d 3) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = ((etaZ (a 0) (a 2) * etaZ (a 1) (a 3) : ℤ) : ℂ) := by
  have key : ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 2) * etaZ (d 1) (d 3) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = (∑ x : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3, ((etaZ x z : ℤ) : ℂ)
            * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 2) z : ℝ) : ℂ)))
        * (∑ y : Fin 1 ⊕ Fin 3, ∑ w : Fin 1 ⊕ Fin 3, ((etaZ y w : ℤ) : ℂ)
            * (((Λ.1 (a 1) y : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
    rw [sum_pi_four]
    have hterm : ∀ x y z w : Fin 1 ⊕ Fin 3,
        ((etaZ (![x, y, z, w] 0) (![x, y, z, w] 2)
            * etaZ (![x, y, z, w] 1) (![x, y, z, w] 3) : ℤ) : ℂ)
          * ∏ i, ((Λ.1 (a i) (![x, y, z, w] i) : ℝ) : ℂ)
        = (((etaZ x z : ℤ) : ℂ) * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 2) z : ℝ) : ℂ)))
          * (((etaZ y w : ℤ) : ℂ)
            * (((Λ.1 (a 1) y : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
      intro x y z w
      simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      push_cast
      ring
    simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [key, sum_etaZ_mul, sum_etaZ_mul]
  push_cast
  ring

/-- The split pairing of two metrics is carried to itself by a Lorentz matrix. -/
lemma sum_splitPair_mul (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 3) * etaZ (d 1) (d 2) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = ((etaZ (a 0) (a 3) * etaZ (a 1) (a 2) : ℤ) : ℂ) := by
  have key : ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 3) * etaZ (d 1) (d 2) : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = (∑ x : Fin 1 ⊕ Fin 3, ∑ w : Fin 1 ⊕ Fin 3, ((etaZ x w : ℤ) : ℂ)
            * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ)))
        * (∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3, ((etaZ y z : ℤ) : ℂ)
            * (((Λ.1 (a 1) y : ℝ) : ℂ) * ((Λ.1 (a 2) z : ℝ) : ℂ))) := by
    rw [sum_pi_four]
    have hterm : ∀ x y z w : Fin 1 ⊕ Fin 3,
        ((etaZ (![x, y, z, w] 0) (![x, y, z, w] 3)
            * etaZ (![x, y, z, w] 1) (![x, y, z, w] 2) : ℤ) : ℂ)
          * ∏ i, ((Λ.1 (a i) (![x, y, z, w] i) : ℝ) : ℂ)
        = (((etaZ x w : ℤ) : ℂ) * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ)))
          * (((etaZ y z : ℤ) : ℂ)
            * (((Λ.1 (a 1) y : ℝ) : ℂ) * ((Λ.1 (a 2) z : ℝ) : ℂ))) := by
      intro x y z w
      simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      push_cast
      ring
    simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [key, sum_etaZ_mul, sum_etaZ_mul]
  push_cast
  ring

set_option maxRecDepth 100000 in
/-- The Levi-Civita sign is a determinant: it is the determinant of the Kronecker
  matrix of the multi-index against the standard listing of the four directions. A
  finite check over the `256` multi-indices. -/
lemma det_delta_eq_epsilonSignZ_int (b : Fin 4 → Fin 1 ⊕ Fin 3) :
    (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 =>
      if b (finSumFinEquiv μ) = ν then (1 : ℤ) else 0).det = epsilonSignZ b := by
  revert b
  decide

/-- The determinant form of the Levi-Civita sign over any commutative ring, the integer
  identity carried along the ring map from `ℤ`. -/
lemma det_delta_eq_epsilonSignZ {R : Type*} [CommRing R] (b : Fin 4 → Fin 1 ⊕ Fin 3) :
    (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 =>
      if b (finSumFinEquiv μ) = ν then (1 : R) else 0).det = ((epsilonSignZ b : ℤ) : R) := by
  have h := RingHom.map_det (Int.castRingHom R)
    (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 => if b (finSumFinEquiv μ) = ν then (1 : ℤ) else 0)
  simp only [Int.coe_castRingHom, RingHom.mapMatrix_apply] at h
  rw [← det_delta_eq_epsilonSignZ_int b, h]
  congr 1
  ext μ ν
  by_cases hbν : b (finSumFinEquiv μ) = ν <;> simp [Matrix.map_apply, hbν]

/-- The Leibniz formula with the permutation moving the column index. -/
lemma det_eq_sum_perm_prod {R : Type*} [CommRing R]
    (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) R) :
    X.det = ∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 3),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ μ, X μ (σ μ) := by
  rw [← Matrix.det_transpose X, Matrix.det_apply']
  rfl

/-- The Levi-Civita sign transforms by the determinant: contracting it against four rows
  of a matrix returns the determinant times the sign of the rows. Both sides are the
  determinant of the matrix whose rows are those of `M` selected by `a`, the left one
  after expanding each row in the standard directions and the right one after the
  product rule for determinants. -/
lemma sum_epsilonSignZ_mul_prod {R : Type*} [CommRing R]
    (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) R) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : R) * ∏ i, M (a i) (d i)
      = M.det * ((epsilonSignZ a : ℤ) : R) := by
  classical
  have hre : ∀ (σ : Equiv.Perm (Fin 1 ⊕ Fin 3)) (d : Fin 4 → Fin 1 ⊕ Fin 3),
      (∏ μ, (if d (finSumFinEquiv μ) = σ μ then (1 : R) else 0))
        = ∏ i, (if d i = σ (finSumFinEquiv.symm i) then (1 : R) else 0) := by
    intro σ d
    rw [← Equiv.prod_comp finSumFinEquiv
      (fun i => if d i = σ (finSumFinEquiv.symm i) then (1 : R) else 0)]
    exact Finset.prod_congr rfl fun μ _ => by rw [Equiv.symm_apply_apply]
  have hprod : ∀ (σ : Equiv.Perm (Fin 1 ⊕ Fin 3)) (d : Fin 4 → Fin 1 ⊕ Fin 3),
      (∏ μ, (if d (finSumFinEquiv μ) = σ μ then (1 : R) else 0)) * ∏ i, M (a i) (d i)
        = ∏ i, ((if d i = σ (finSumFinEquiv.symm i) then (1 : R) else 0)
          * M (a i) (d i)) := by
    intro σ d
    rw [hre σ d, ← Finset.prod_mul_distrib]
  calc ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : R) * ∏ i, M (a i) (d i)
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 3),
          ((Equiv.Perm.sign σ : ℤ) : R)
            * ∏ i, ((if d i = σ (finSumFinEquiv.symm i) then (1 : R) else 0)
              * M (a i) (d i)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← det_delta_eq_epsilonSignZ (R := R) d, det_eq_sum_perm_prod, Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [Matrix.of_apply]
        rw [mul_assoc, hprod σ d]
    _ = ∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 3), ((Equiv.Perm.sign σ : ℤ) : R)
          * ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
            ∏ i, ((if d i = σ (finSumFinEquiv.symm i) then (1 : R) else 0)
              * M (a i) (d i)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 3), ((Equiv.Perm.sign σ : ℤ) : R)
          * ∏ i, M (a i) (σ (finSumFinEquiv.symm i)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        congr 1
        have hpi := Finset.sum_prod_piFinset (ι := Fin 4) (κ := Fin 1 ⊕ Fin 3) Finset.univ
          (fun i ν => (if ν = σ (finSumFinEquiv.symm i) then (1 : R) else 0) * M (a i) ν)
        rw [Fintype.piFinset_univ] at hpi
        rw [hpi]
        exact Finset.prod_congr rfl fun i _ => by simp
    _ = M.det * ((epsilonSignZ a : ℤ) : R) := by
        rw [mul_comm, ← det_delta_eq_epsilonSignZ (R := R) a, ← Matrix.det_mul,
          det_eq_sum_perm_prod]
        refine Finset.sum_congr rfl fun σ _ => ?_
        congr 1
        rw [← Equiv.prod_comp finSumFinEquiv
          (fun i => M (a i) (σ (finSumFinEquiv.symm i)))]
        refine Finset.prod_congr rfl fun μ _ => ?_
        rw [Equiv.symm_apply_apply, Matrix.mul_apply]
        simp

/-- The Levi-Civita sign is carried to itself by a proper Lorentz matrix: the
  determinant factor of `sum_epsilonSignZ_mul_prod` is one. -/
lemma sum_epsilonSignZ_mul (Λ : LorentzGroup 3) (hΛ : Λ.1.det = 1)
    (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : ℂ)
        * ∏ i, ((Λ.1 (a i) (d i) : ℝ) : ℂ)
      = ((epsilonSignZ a : ℤ) : ℂ) := by
  have hdet : (Complex.ofRealHom.mapMatrix Λ.1).det = 1 := by
    rw [← RingHom.map_det, hΛ]
    simp
  have h := sum_epsilonSignZ_mul_prod (Complex.ofRealHom.mapMatrix Λ.1) a
  rw [hdet, one_mul] at h
  rw [← h]
  rfl

/-!

## I.6. The four contractions are Lorentz invariant

A linear map moving the components by a Lorentz matrix fixes any combination of the
components whose coefficient family that matrix fixes, and I.5 says the four coefficient
families are fixed. The statements are made for an arbitrary such map, so that they can
be read in the quotient of J.3 as well as for `repLorentz`; the Levi-Civita one asks in
addition that the matrix be proper, which the matrices coming from `SL(2,ℂ)` are.

-/

/-- A linear map moving the components by a Lorentz matrix fixes every combination of
  the components whose coefficient family that matrix fixes. -/
lemma map_sum_smul_eq_self {f : B →ₗ[ℂ] B} {Λ : LorentzGroup 3}
    (hf : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a)
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (hc : ∀ a : Fin 4 → Fin 1 ⊕ Fin 3,
      ∑ l : Fin 4 → Fin 1 ⊕ Fin 3, c l * ∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ) = c a) :
    f (∑ l : Fin 4 → Fin 1 ⊕ Fin 3, c l • T l)
      = ∑ l : Fin 4 → Fin 1 ⊕ Fin 3, c l • T l := by
  rw [map_sum]
  have h1 : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (c l • T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (c l * ∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a := by
    intro l
    rw [map_smul, hf l, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul, hc a]

/-- The outer contraction is fixed by any linear map moving the components by a Lorentz
  matrix. -/
lemma map_outerContraction {f : B →ₗ[ℂ] B} {Λ : LorentzGroup 3}
    (hf : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (outerContraction (T := T)) = outerContraction (T := T) := by
  rw [outerContraction]
  exact map_sum_smul_eq_self hf _ (sum_outerPair_mul Λ)

/-- The inner contraction is fixed by any linear map moving the components by a Lorentz
  matrix. -/
lemma map_innerContraction {f : B →ₗ[ℂ] B} {Λ : LorentzGroup 3}
    (hf : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (innerContraction (T := T)) = innerContraction (T := T) := by
  rw [innerContraction]
  exact map_sum_smul_eq_self hf _ (sum_innerPair_mul Λ)

/-- The split contraction is fixed by any linear map moving the components by a Lorentz
  matrix. -/
lemma map_splitContraction {f : B →ₗ[ℂ] B} {Λ : LorentzGroup 3}
    (hf : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (splitContraction (T := T)) = splitContraction (T := T) := by
  rw [splitContraction]
  exact map_sum_smul_eq_self hf _ (sum_splitPair_mul Λ)

/-- The Levi-Civita contraction is fixed by any linear map moving the components by a
  proper Lorentz matrix. Properness cannot be dropped: an improper matrix negates the
  Levi-Civita sign, and with it the contraction. -/
lemma map_epsilonContraction {f : B →ₗ[ℂ] B} {Λ : LorentzGroup 3} (hΛ : Λ.1.det = 1)
    (hf : ∀ l : Fin 4 → Fin 1 ⊕ Fin 3, f (T l)
      = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (∏ i, ((Λ.1 (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (epsilonContraction (T := T)) = epsilonContraction (T := T) := by
  rw [epsilonContraction]
  exact map_sum_smul_eq_self hf _ (sum_epsilonSignZ_mul Λ hΛ)

include hT in
/-- The outer contraction is Lorentz invariant. -/
lemma repLorentz_outerContraction (g : SL(2,ℂ)) :
    repLorentz g (outerContraction (T := T)) = outerContraction (T := T) :=
  map_outerContraction (Λ := SL2C.toLorentzGroup g) (hT.repLorentz_T g)

include hT in
/-- The inner contraction is Lorentz invariant. -/
lemma repLorentz_innerContraction (g : SL(2,ℂ)) :
    repLorentz g (innerContraction (T := T)) = innerContraction (T := T) :=
  map_innerContraction (Λ := SL2C.toLorentzGroup g) (hT.repLorentz_T g)

include hT in
/-- The split contraction is Lorentz invariant. -/
lemma repLorentz_splitContraction (g : SL(2,ℂ)) :
    repLorentz g (splitContraction (T := T)) = splitContraction (T := T) :=
  map_splitContraction (Λ := SL2C.toLorentzGroup g) (hT.repLorentz_T g)

include hT in
/-- The Levi-Civita contraction is Lorentz invariant, the Lorentz matrix of an element
  of `SL(2,ℂ)` being proper. -/
lemma repLorentz_epsilonContraction (g : SL(2,ℂ)) :
    repLorentz g (epsilonContraction (T := T)) = epsilonContraction (T := T) :=
  map_epsilonContraction (Λ := SL2C.toLorentzGroup g) (SL2C.toLorentzGroup_det_one g)
    (hT.repLorentz_T g)

include hT in
/-- A linear combination of the four contractions is Lorentz invariant. -/
lemma repLorentz_smul_contraction (a₁ a₂ a₃ a₄ : ℂ) (g : SL(2,ℂ)) :
    repLorentz g (a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T))
      = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) := by
  simp only [map_add, map_smul, hT.repLorentz_outerContraction,
    hT.repLorentz_innerContraction, hT.repLorentz_splitContraction,
    hT.repLorentz_epsilonContraction]

include hT in
/-- A linear combination of the four contractions lies in the span of the components. -/
lemma smul_contraction_mem_span (a₁ a₂ a₃ a₄ : ℂ) :
    a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
      + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) ∈ hT.span :=
  add_mem (add_mem (add_mem (Submodule.smul_mem _ _ hT.outerContraction_mem_span)
    (Submodule.smul_mem _ _ hT.innerContraction_mem_span))
    (Submodule.smul_mem _ _ hT.splitContraction_mem_span))
    (Submodule.smul_mem _ _ hT.epsilonContraction_mem_span)

/-!

## J. The classification of the Lorentz invariants

## J.1. Graded extraction along the sieve

An invariant element has weight zero along every axis, so it passes down the sieve of
sections D and E: each covering step keeps only its weight-zero member.

-/

/-- Graded extraction: an element of the join of a family bounded by the boost-weight
  grading which itself has weight zero lies in the zero member of the family. -/
lemma mem_of_mem_iSup_of_boostWeight_zero {i : Fin 3} {S : ℤ → Submodule ℂ B}
    (hS : ∀ m : ℤ, S m ≤ boostWeightSubmodule repLorentz i m) {x : B}
    (hx : x ∈ ⨆ m, S m) (h0 : x ∈ boostWeightSubmodule repLorentz i 0) : x ∈ S 0 := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  have hkey := eq_component_zero_of_mem_boostWeightSubmodule (i := i)
    (s := insert 0 f.support) (w := fun m => f m) h0
    (fun m _ => hS m (hf m)) (Finset.mem_insert_self 0 _) ?_
  · rw [hkey]
    exact hf 0
  · rw [Finsupp.sum]
    by_cases h : (0 : ℤ) ∈ f.support
    · rw [Finset.insert_eq_self.2 h]
    · rw [Finset.sum_insert h, Finsupp.notMem_support_iff.1 h, zero_add]

/-- Invariance gives boost weight zero: an element fixed by the Lorentz group lies in
  the weight-zero space of every boost axis. -/
lemma mem_boostWeightSubmodule_zero_of_invariant {x : B}
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) (i : Fin 3) :
    x ∈ boostWeightSubmodule repLorentz i 0 := by
  rw [mem_boostWeightSubmodule]
  intro t ht
  rw [hinv, zpow_zero, one_smul]

/-!

## J.2. The classification

-/

include hT in
/-- Every Lorentz-invariant element is an orbit-sum combination: an element of the
  span of the components fixed by the Lorentz group is a combination of the orbit sums
  of the `22` canonical representatives. -/
theorem exists_eq_sum_orbitRep_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : Fin 22 → ℂ, x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k) := by
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h1 : x ∈ hT.boostPiece 0 0 := by
    refine mem_of_mem_iSup_of_boostWeight_zero (i := 0)
      (hT.boostPiece_le_boostWeightSubmodule 0) ?_ (hw 0)
    rw [← hT.span_eq_iSup_boostPiece 0]
    exact hx
  have h2 : x ∈ hT.boostPiece₂ 0 1 0 0 :=
    mem_of_mem_iSup_of_boostWeight_zero (i := 1)
      (hT.boostPiece₂_le_boostWeightSubmodule 0 1 0)
      (hT.boostPiece_le_iSup_boostPiece₂ 0 1 0 h1) (hw 1)
  have h3 : x ∈ hT.boostPiece₃ 0 :=
    mem_of_mem_iSup_of_boostWeight_zero (i := 2)
      hT.boostPiece₃_le_boostWeightSubmodule
      (hT.boostPiece₂_le_iSup_boostPiece₃ h2) (hw 2)
  have h4 : x ∈ pairedOrDistinctSubmodule (T := T) :=
    hT.boostPiece₃_zero_le_iSup_pairedOrDistinct h3
  have havg : rotationAverage (repLorentz := repLorentz) x = x := by
    rw [rotationAverage]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    rw [hinv rotationCycle, hinv (rotationCycle ^ 2)]
    module
  have h5 : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T) :=
    havg ▸ Submodule.mem_map_of_mem h4
  obtain ⟨c, hc⟩ := hT.exists_eq_sum_rotationSubset_of_mem_rotationSubmodule h5
  refine ⟨fun k => c (orbitRep k), ?_⟩
  rw [hc, sum_rotationSubset (fun d => c d • rotationOrbitSum (T := T) d)]

include hT in
/-- The classification of the Lorentz invariants: every element of the span of the
  components fixed by the Lorentz group is a linear combination of the outer, inner and
  split metric contractions and the Levi-Civita contraction. -/
theorem exists_smul_contraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ,
      x = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) := by
  obtain ⟨c, hc⟩ := hT.exists_eq_sum_orbitRep_of_invariant hx hinv
  exact hT.exists_smul_contraction_of_eq_sum_orbitRep c hc
    (mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv)

include hT in
/-- The classification read as an equivalence: an element of the span of the components
  is fixed by the Lorentz group exactly when it is a linear combination of the four
  contractions. The forward direction is the classification, the backward one the
  invariance of the four contractions of I.6. -/
theorem mem_span_and_invariant_iff (x : B) :
    (x ∈ hT.span ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ a₁ a₂ a₃ a₄ : ℂ,
        x = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
          + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) := by
  refine ⟨fun h => hT.exists_smul_contraction_of_invariant h.1 h.2, ?_⟩
  rintro ⟨a₁, a₂, a₃, a₄, rfl⟩
  exact ⟨hT.smul_contraction_mem_span a₁ a₂ a₃ a₄,
    hT.repLorentz_smul_contraction a₁ a₂ a₃ a₄⟩


/-!

## J.3. The classification modulo a Lorentz-stable submodule

A Lorentz-stable submodule can be divided out: the quotient representation carries the
images of the components as a quadruple Lorentz tensor again, so the classification
applies verbatim in the quotient and lifts to a classification modulo the submodule.
Stability of the submodule is what makes the quotient representation exist, and it
cannot be dropped: for an unstable line the only invariant of the line is `0`, while an
invariant of the sum may well lie outside the span. The error term is invariant for
free, being the difference of two invariants, the element and the combination of the
four contractions, which I.6 shows to be invariant.

-/

/-- The representation induced on the quotient by a Lorentz-stable submodule. -/
noncomputable def quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    Representation ℂ SL(2,ℂ) (B ⧸ S) where
  toFun g := S.mapQ S (repLorentz g) fun y hy => hS g y hy
  map_one' := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

@[simp]
lemma quotRep_mkQ (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (g : SL(2,ℂ)) (y : B) :
    quotRep (repLorentz := repLorentz) S hS g (S.mkQ y) = S.mkQ (repLorentz g y) := rfl

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a quadruple Lorentz tensor. -/
lemma isQuadLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsQuadLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the outer contraction to the outer contraction of the
  images. -/
lemma mkQ_outerContraction (S : Submodule ℂ B) :
    S.mkQ (outerContraction (T := T)) = outerContraction (T := fun l => S.mkQ (T l)) := by
  rw [outerContraction, outerContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

/-- The quotient map carries the inner contraction to the inner contraction of the
  images. -/
lemma mkQ_innerContraction (S : Submodule ℂ B) :
    S.mkQ (innerContraction (T := T)) = innerContraction (T := fun l => S.mkQ (T l)) := by
  rw [innerContraction, innerContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

/-- The quotient map carries the split contraction to the split contraction of the
  images. -/
lemma mkQ_splitContraction (S : Submodule ℂ B) :
    S.mkQ (splitContraction (T := T)) = splitContraction (T := fun l => S.mkQ (T l)) := by
  rw [splitContraction, splitContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

/-- The quotient map carries the Levi-Civita contraction to the Levi-Civita contraction
  of the images. -/
lemma mkQ_epsilonContraction (S : Submodule ℂ B) :
    S.mkQ (epsilonContraction (T := T)) = epsilonContraction (T := fun l => S.mkQ (T l)) := by
  rw [epsilonContraction, epsilonContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

include hT in
/-- The classification of the Lorentz invariants modulo a stable submodule: an
  element of the span of the components together with a Lorentz-stable submodule `S`,
  fixed by the Lorentz group, is a linear combination of the four contractions up to an
  error in `S`, and the error is Lorentz invariant as well, being the difference of two
  invariants. The classification is applied in the quotient by `S`, where the images
  of the components form a quadruple Lorentz tensor again. -/
lemma exists_smul_contraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
      x = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) + y
      ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  have hT' := hT.isQuadLorentz_quotRep S hS
  -- the class of `x` lies in the span of the images of the components
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  -- and is invariant for the quotient action
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  obtain ⟨a₁, a₂, a₃, a₄, hcomb⟩ := hT'.exists_smul_contraction_of_invariant hmk hinv'
  rw [← mkQ_outerContraction, ← mkQ_innerContraction, ← mkQ_splitContraction,
    ← mkQ_epsilonContraction] at hcomb
  refine ⟨a₁, a₂, a₃, a₄, x - (a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
    + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T)), ?_, by abel,
    fun g => ?_⟩
  · have hker : x - (a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
        + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T))
        ∈ LinearMap.ker S.mkQ := by
      rw [LinearMap.mem_ker, map_sub, hcomb]
      simp only [map_add, map_smul]
      abel
    rwa [Submodule.ker_mkQ] at hker
  · rw [map_sub, hinv g, hT.repLorentz_smul_contraction a₁ a₂ a₃ a₄ g]

include hT in
/-- The classification modulo a stable submodule read as an equivalence: a vector of the
  span joined with a Lorentz-stable submodule `S` is fixed by the Lorentz group exactly
  when it is a linear combination of the four contractions up to an invariant error in
  `S`. The forward direction is `exists_smul_contraction_of_invariant_subset`, the
  backward one the invariance of the four contractions of I.6. -/
theorem mem_span_sup_invariant_iff (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
        x = a₁ • outerContraction (T := T) + a₂ • innerContraction (T := T)
          + a₃ • splitContraction (T := T) + a₄ • epsilonContraction (T := T) + y
        ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  refine ⟨fun h => hT.exists_smul_contraction_of_invariant_subset S hS h.1 h.2, ?_⟩
  rintro ⟨a₁, a₂, a₃, a₄, y, hyS, rfl, hyinv⟩
  refine ⟨add_mem (Submodule.mem_sup_left (hT.smul_contraction_mem_span a₁ a₂ a₃ a₄))
    (Submodule.mem_sup_right hyS), fun g => ?_⟩
  rw [map_add, hT.repLorentz_smul_contraction a₁ a₂ a₃ a₄ g, hyinv g]

end IsQuadLorentz

end Lorentz
