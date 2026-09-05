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
# Lorentz invariants of a single four-vector index

`IsSingleLorentz repLorentz T` says that a family `T`, indexed by a single four-vector
index and valued in a module `B` carrying a representation of `SL(2,ℂ)`, transforms as
a vector `T^{μ}`.

One index admits no invariant contraction at all: the metric needs two indices and the
Levi-Civita symbol four. The main theorem `eq_zero_of_invariant` says accordingly that
every Lorentz invariant in the span of the components is zero.

The proof is the one-index shadow of `IsBiLorentz`, and is short enough to do without
the certificate polynomial that the two- and four-index cases need. Along a spatial
axis the four light-cone components carry boost weights `2`, `-2`, `0` and `0`, and the
two weight-zero ones are the directions transverse to both time and that axis. An
invariant has boost weight zero along every axis, so one round of the weight-zero
projection along axis `i` kills every coefficient outside the transverse pair of that
axis; running the three axes in turn leaves nothing, because no direction is transverse
to all three axes at once.

The section headings tell the story: the light-cone basis along one axis (B) grades the
span by boost weight, the weight-zero projection of a generator is the transverse
projector (C), and chaining the three axes annihilates an invariant (D), which then
also holds modulo a Lorentz-stable submodule (E).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (lightConeCoeffZ coe_lightConeCoeffZ lightConeCoeffInvQ
  coe_lightConeCoeffInvQ lightConeCoeffInvZ coe_lightConeCoeffInvZ
  eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. Single Lorentz tensors and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by a single four-vector index, transforms
  as a vector `T^{μ}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsSingleLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 1 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 1), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsSingleLorentz
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsSingleLorentz B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsSingleLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The span of the components is exactly the set of linear combinations of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 1 → (Fin 1 ⊕ Fin 3)) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 1 → (Fin 1 ⊕ Fin 3)) → ℂ, y = ∑ d, c d • T d)
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

Along a spatial axis `i` the coordinate components recombine into the light-cone
components `lightCone i c`, which span the same space and are homogeneous of boost
weight `∑ j, lightConeWeight (c j)`.

-/

/-- The axis-`i` light-cone component of `T` at the light-cone multi-index `c`. -/
noncomputable def lightCone (hT : IsSingleLorentz B repLorentz T) (i : Fin 3)
    (c : Fin 1 → Fin 4) : B :=
  ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the coordinate components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 1 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the light-cone components along any axis. -/
lemma eq_sum_lightCone (i : Fin 3) (d : Fin 1 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 1 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 1 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 1 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The light-cone components along any axis span the same space as the components. -/
lemma span_eq_lightCone (hT : IsSingleLorentz B repLorentz T) (i : Fin 3) :
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
lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 1 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ x : Fin 1 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x)
        = ∑ a : Fin 1 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ x : Fin 1 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 1 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 1 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 1 → Fin 1 ⊕ Fin 3, (((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        exact sum_prod_lightConeCoeff i c a ht
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-!

## C. The weight-zero round along one axis

## C.1. The boost-weight components of a generator

Each generator `T e` is the sum of its boost-weight components `monoComponent i e m`,
and with one index the possible weights are just `-2`, `0` and `2`.

-/

/-- The axis-`i` weight-`m` component of the generator `T e`: the weight-`m` partial
  sum of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3)
    (m : ℤ) : hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The light-cone weight of a single slot is `-2`, `0` or `2`. -/
lemma sum_lightConeWeight_mem (c : Fin 1 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-2, 0, 2} : Finset ℤ) := by
  have hweight : ∀ κ : Fin 4, lightConeWeight κ ∈ ({-2, 0, 2} : Finset ℤ) := by decide
  rw [Fin.sum_univ_one]
  exact hweight (c 0)

/-- A component is the sum of its weight components over the three possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

/-!

## C.2. The weight-zero transition matrix

The matrix of the axis-`i` weight-zero projection in the `T`-basis, and its integer
mirror, whose closed form is the projector onto the two transverse directions.

-/

/-- The matrix of the axis-`i` weight-zero projection in the `T`-basis: the coefficient
  of `T d` in the re-expansion of `monoComponent i e 0` through the light-cone basis. -/
def weightZeroTransition (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ)

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i e 0` is the
  `e`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) :
    hT.monoComponent i e 0
      = ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, ((weightZeroTransition i d e : ℚ) : ℂ) • T d := by
  rw [monoComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [weightZeroTransition]
  push_cast
  simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ, Finset.prod_mul_distrib]

/-- Integer mirror of the weight-zero transition: twice its value. -/
def weightZeroTransitionZ (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) : ℤ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvZ i (e s) (c s) * lightConeCoeffZ i (c s) (d s)

/-- The integer mirror casts to twice the weight-zero transition. -/
lemma coe_weightZeroTransitionZ (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    ((weightZeroTransitionZ i d e : ℤ) : ℚ) = 2 * weightZeroTransition i d e := by
  rw [weightZeroTransitionZ, weightZeroTransition]
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
    _ = 2 * ∏ s, lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        norm_num [Finset.card_univ]

/-- The closed form of the integer weight-zero transition: twice the projector onto the
  two directions transverse to both the time direction and the axis `i`. -/
lemma weightZeroTransitionZ_eq (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    weightZeroTransitionZ i d e
      = if e 0 = d 0 ∧ (d 0 = Sum.inr (i + 1) ∨ d 0 = Sum.inr (i + 2)) then 2 else 0 := by
  revert i
  revert d e
  decide

/-- The closed form of the weight-zero transition: the projector onto the two
  directions transverse to both the time direction and the axis `i`. -/
lemma weightZeroTransition_eq (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition i d e
      = if e 0 = d 0 ∧ (d 0 = Sum.inr (i + 1) ∨ d 0 = Sum.inr (i + 2)) then 1 else 0 := by
  have h := coe_weightZeroTransitionZ i d e
  rw [weightZeroTransitionZ_eq] at h
  split_ifs at h ⊢ <;> push_cast at h <;> linarith

/-!

## C.3. The transverse support of one round

-/

include hT in
/-- One round of the recursion along one axis: an element of weight zero along axis `i`
  expanded in the generators re-expands with the weight-zero transition matrix applied
  to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
  have hsum : x = ∑ m ∈ ({-2, 0, 2} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i e m :=
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

/-- The weight-zero transition acting on a coefficient vector keeps the coefficients at
  the two directions transverse to the axis `i` and discards the rest. -/
lemma sum_weightZeroTransition_mul (i : Fin 3) (d : Fin 1 → Fin 1 ⊕ Fin 3)
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) :
    ∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e
      = if d 0 = Sum.inr (i + 1) ∨ d 0 = Sum.inr (i + 2) then c d else 0 := by
  by_cases htr : d 0 = Sum.inr (i + 1) ∨ d 0 = Sum.inr (i + 2)
  · rw [if_pos htr]
    have hterm : ∀ e : Fin 1 → Fin 1 ⊕ Fin 3,
        ((weightZeroTransition i d e : ℚ) : ℂ) * c e = if e = d then c e else 0 := by
      intro e
      rw [weightZeroTransition_eq]
      by_cases he : e = d
      · subst he
        simp [htr]
      · have h0 : e 0 ≠ d 0 := fun h =>
          he (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
        simp [h0, he]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg htr]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [weightZeroTransition_eq, if_neg (fun h => htr h.2)]
    simp

include hT in
/-- One round in support form: an element of weight zero along axis `i` re-expands with
  every coefficient outside the transverse pair of that axis set to zero. -/
lemma eq_sum_transverse_smul (i : Fin 3) {x : B}
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (if d 0 = Sum.inr (i + 1) ∨ d 0 = Sum.inr (i + 2) then c d else 0) • T d := by
  rw [hT.eq_sum_weightZeroTransition_smul i c hx hw]
  exact Finset.sum_congr rfl fun d _ => by rw [sum_weightZeroTransition_mul]

/-!

## D. The classification of the Lorentz invariants

No direction is transverse to all three axes, so chaining the three rounds of section
C.3 annihilates every invariant.

-/

/-- No four-vector direction is transverse to all three spatial axes at once. -/
lemma not_transverse_all (μ : Fin 1 ⊕ Fin 3) :
    ¬((μ = Sum.inr ((0 : Fin 3) + 1) ∨ μ = Sum.inr ((0 : Fin 3) + 2)) ∧
      (μ = Sum.inr ((1 : Fin 3) + 1) ∨ μ = Sum.inr ((1 : Fin 3) + 2)) ∧
      (μ = Sum.inr ((2 : Fin 3) + 1) ∨ μ = Sum.inr ((2 : Fin 3) + 2))) := by
  revert μ
  decide

include hT in
/-- The classification of the Lorentz invariants: a single four-vector index carries no
  invariant contraction, so every element of the span of the components fixed by the
  Lorentz group is zero. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h0 := hT.eq_sum_transverse_smul 0 c hc (hw 0)
  have h1 := hT.eq_sum_transverse_smul 1
    (fun d => if d 0 = Sum.inr ((0 : Fin 3) + 1) ∨ d 0 = Sum.inr ((0 : Fin 3) + 2)
      then c d else 0) h0 (hw 1)
  have h2 := hT.eq_sum_transverse_smul 2
    (fun d => if d 0 = Sum.inr ((1 : Fin 3) + 1) ∨ d 0 = Sum.inr ((1 : Fin 3) + 2)
      then (if d 0 = Sum.inr ((0 : Fin 3) + 1) ∨ d 0 = Sum.inr ((0 : Fin 3) + 2)
        then c d else 0) else 0) h1 (hw 2)
  rw [h2]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h2t : d 0 = Sum.inr ((2 : Fin 3) + 1) ∨ d 0 = Sum.inr ((2 : Fin 3) + 2)
  · rw [if_pos h2t]
    by_cases h1t : d 0 = Sum.inr ((1 : Fin 3) + 1) ∨ d 0 = Sum.inr ((1 : Fin 3) + 2)
    · rw [if_pos h1t]
      by_cases h0t : d 0 = Sum.inr ((0 : Fin 3) + 1) ∨ d 0 = Sum.inr ((0 : Fin 3) + 2)
      · exact absurd ⟨h0t, h1t, h2t⟩ (not_transverse_all (d 0))
      · rw [if_neg h0t, zero_smul]
    · rw [if_neg h1t, zero_smul]
  · rw [if_neg h2t, zero_smul]

/-!

## E. The classification modulo a Lorentz-stable submodule

A Lorentz-stable submodule can be divided out: the quotient representation carries the
images of the components as a single Lorentz tensor again, so the classification
applies verbatim in the quotient and lifts to a classification modulo the submodule.
The quotient representation itself is the one built in `IsQuadLorentz`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a single Lorentz tensor. -/
lemma isSingleLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsSingleLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
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
  have hT' := hT.isSingleLorentz_quotRep S hS
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

end IsSingleLorentz

end Lorentz
