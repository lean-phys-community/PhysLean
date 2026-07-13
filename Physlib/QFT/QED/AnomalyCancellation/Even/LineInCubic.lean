/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.LineInPlaneCond
/-!

# Line In Cubic Even case

We say that a linear solution satisfies the `lineInCubic` property
if the line through that point and through the two different planes formed by the basis of
`LinSols` lies in the cubic.

We show that for a solution all its permutations satisfy this property, then there exists
a permutation for which it lies in the plane spanned by the first part of the basis.

The main reference for this file is:

- https://arxiv.org/pdf/1912.04804.pdf
-/

@[expose] public section

namespace PureU1
namespace Even

open BigOperators

variable {n : ℕ}
open VectorLikeEvenPlane

/-- A property on `LinSols`, satisfied if every point on the line between the two planes
in the basis through that point is in the cubic. -/
def LineInCubic (S : (PureU1 (2 * n.succ)).LinSols) : Prop :=
  ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = Pa g f) (a b : ℚ),
  accCube (2 * n.succ) (a • P g + b • P! f) = 0

set_option backward.isDefEq.respectTransparency false in
lemma lineInCubic_expand {S : (PureU1 (2 * n.succ)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = Pa g f) (a b : ℚ),
    3 * a * b * (a * accCubeTriLinSymm (P g) (P g) (P! f)
    + b * accCubeTriLinSymm (P! f) (P! f) (P g)) = 0 := by
  intro g f hS a b
  have h1 := h g f hS a b
  change accCubeTriLinSymm.toCubic (a • P g + b • P! f) = 0 at h1
  simp only [TriLinearSymm.toCubic_add, HomogeneousCubic.map_smul,
    accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂, accCubeTriLinSymm.map_smul₃] at h1
  erw [P_accCube, P!_accCube] at h1
  linear_combination h1

/--
This lemma states that for a given `S` of type `(PureU1 (2 * n.succ)).AnomalyFreeLinear` and
a proof `h` that the line through `S` lies on a cubic curve,
for any functions `g : Fin n.succ → ℚ` and `f : Fin n → ℚ`, if `S.val = P g + P! f`,
then `accCubeTriLinSymm.toFun (P g, P g, P! f) = 0`.
-/
lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n.succ)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = P g + P! f),
    accCubeTriLinSymm (P g) (P g) (P! f) = 0 := by
  intro g f hS
  linear_combination 2 / 3 * (lineInCubic_expand h g f hS 1 1) -
    (lineInCubic_expand h g f hS 1 2) / 6

/-- A `LinSol` satisfies `LineInCubicPerm` if all its permutations satisfy `lineInCubic`. -/
def LineInCubicPerm (S : (PureU1 (2 * n.succ)).LinSols) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n.succ)).group),
  LineInCubic ((FamilyPermutations (2 * n.succ)).linSolRep M S)

/-- If `lineInCubicPerm S` then `lineInCubic S`. -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n.succ)).LinSols}
    (hS : LineInCubicPerm S) : LineInCubic S := hS 1

/-- If `lineInCubicPerm S` then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n.succ)).LinSols}
    (hS : LineInCubicPerm S) (M' : (FamilyPermutations (2 * n.succ)).group) :
    LineInCubicPerm ((FamilyPermutations (2 * n.succ)).linSolRep M' S) := by
  intro M
  have h := hS (M * M')
  erw [(FamilyPermutations (2 * n.succ)).linSolRep.map_mul M M'] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ)).LinSols}
    (LIC : LineInCubicPerm S) :
    ∀ (j : Fin n) (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = Pa g f),
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j))
      * accCubeTriLinSymm (P g) (P g) (basis!AsCharges j) = 0 := by
  intro j g f h
  obtain ⟨g', f', hall⟩ := span_basis_swap! j rfl g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P!
    (lineInCubicPerm_self (lineInCubicPerm_permute LIC
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2, accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ)).LinSols}
    (f : Fin n.succ.succ → ℚ) (g : Fin n.succ → ℚ) (hS : S.val = Pa f g) :
    accCubeTriLinSymm (P f) (P f) (basis!AsCharges (Fin.last n)) =
    - (S.val (evenShiftSnd (Fin.last n)) + S.val (evenShiftFst (Fin.last n))) *
    (2 * S.val evenShiftLast +
    S.val (evenShiftSnd (Fin.last n)) + S.val (evenShiftFst (Fin.last n))) := by
  rw [P_P_P!_accCube f (Fin.last n), hS, Pa_evenShiftSnd, Pa_evenShiftFst, Pa_evenShiftLast,
    Fin.succ_last]
  ring

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ)).LinSols}
    (LIC : LineInCubicPerm S) :
    LineInPlaneProp
    ((S.val (evenShiftSnd (Fin.last n))), ((S.val (evenShiftFst (Fin.last n))),
      (S.val evenShiftLast))) := by
  obtain ⟨g, f, hfg⟩ := span_basis S
  have h1 := lineInCubicPerm_swap LIC (Fin.last n) g f hfg
  rw [P_P_P!_accCube' g f hfg] at h1
  simp only [Nat.succ_eq_add_one, neg_add_rev, mul_eq_zero] at h1
  rcases h1 with h1 | h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (Or.inl (by linear_combination -(1 * h1)))
  · exact Or.inr (Or.inr h1)

lemma lineInCubicPerm_last_perm {S : (PureU1 (2 * n.succ.succ)).LinSols}
    (LIC : LineInCubicPerm S) : LineInPlaneCond S := by
  refine @Prop_three (2 * n.succ.succ) LineInPlaneProp S
    (evenShiftSnd (Fin.last n)) (evenShiftFst (Fin.last n))
    evenShiftLast ?_ ?_ ?_ ?_
  · simp [Fin.ext_iff, evenShiftSnd, evenShiftFst]
  · simp [Fin.ext_iff, evenShiftSnd, evenShiftLast]
  · simp [Fin.ext_iff, evenShiftFst, evenShiftLast]
    omega
  · exact fun M => lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M)

lemma lineInCubicPerm_constAbs {S : (PureU1 (2 * n.succ.succ)).Sols}
    (LIC : LineInCubicPerm S.1.1) : ConstAbs S.val :=
  linesInPlane_constAbs_AF S (lineInCubicPerm_last_perm LIC)

theorem lineInCubicPerm_vectorLike {S : (PureU1 (2 * n.succ.succ)).Sols}
    (LIC : LineInCubicPerm S.1.1) : VectorLikeEven S.val :=
  ConstAbs.boundary_value_even S.1.1 (lineInCubicPerm_constAbs LIC)

theorem lineInCubicPerm_in_plane (S : (PureU1 (2 * n.succ.succ)).Sols)
    (LIC : LineInCubicPerm S.1.1) : ∃ (M : (FamilyPermutations (2 * n.succ.succ)).group),
    (FamilyPermutations (2 * n.succ.succ)).linSolRep M S.1.1
    ∈ Submodule.span ℚ (Set.range basis) :=
  vectorLikeEven_in_span S.1.1 (lineInCubicPerm_vectorLike LIC)

end Even
end PureU1
