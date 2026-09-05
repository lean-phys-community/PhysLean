/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLorentz
public import Physlib.Relativity.PauliMatrices.AsTensor
/-!
# Lorentz invariants of a four-vector index and a left-right Weyl pair

`IsVectorLeftRightWeyl repLorentz T` says that a family `T`, indexed by one four-vector
index and by one left-handed and one right-handed Weyl index, and valued in a module `B`
carrying a representation of `SL(2,ℂ)`, transforms as a tensor `T^{μ α α'}`.

This is the shape of the fermion kinetic term, and it is the reason the classifier
exists: the kinetic term is the one Standard Model invariant that ties a vector index to
a pair of opposite-chirality spinor indices, `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`. No other
classifier covers that combination, and it is what the fermion sector needs at mass
weight eight, where the invariants of `derivSubmodule 0 * derivSubmodule 1` are
classified.

There is exactly one invariant here, the contraction against the Pauli matrices: a pair
of opposite-chirality Weyl indices carries the `(1/2, 1/2)` representation, which is the
four-vector representation, so the three indices together are two four-vector indices,
and two four-vector indices admit only the metric trace. The main theorem
`exists_smul_pauliContraction_of_invariant` says accordingly that every Lorentz invariant
in the span of the components is a scalar multiple of `pauliContraction`, and
`repLorentz_pauliContraction` checks that this contraction really is invariant.

The proof makes that argument literal rather than redoing the boost-weight analysis. The
covariant Pauli matrices `σ_μ` intertwine the two index laws — this is
`SL2C.toSelfAdjointMap_basis`, read entrywise — so contracting the Weyl pair against them
turns `T` into a genuine bi-Lorentz tensor, and the Fierz completeness relation makes that
contraction invertible, so the span is unchanged. `IsBiLorentz` then supplies the whole
classification, and its metric trace is on the nose the Pauli contraction of `T`.

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices
carry the contragredient of the laws above. Following `IsBiLeftWeyl`, the symplectic form
`ε` bridges the gap: it is inner for `SL(2,ℂ)`, so re-indexing the two spinor slots by `ε`
converts the contragredient law into the fundamental one without touching the
representation. Here no conjugation twist is needed either, because the mixed law already
carries one conjugate factor and `ε` has real entries. The derivative slot keeps the plain
Lorentz law, since in the Standard Model only the value index of a symbol is dualised. The
re-index does move the contraction: it sends the Pauli matrices to their transposes, so
the invariant named in the dual conclusions is the conjugate Pauli contraction
`pauliBarContraction`, with the scalar `+1`.

The section headings tell the story: the covariant and conjugate Pauli matrices and the
two identities they satisfy (A), the families and the span of their components (B), the
reduction which turns the Weyl pair into a second four-vector index (C), the
classification it buys (D), the model family whose Pauli contraction is
`PauliMatrix.asTensor` (E), the dual index laws and the `ε` re-index which straightens
them out (F, G), and the classification of the invariants of the dual families (H). The
mass-weight-six statement lives in F and H too: a dual left-right Weyl pair with no vector
index has no invariant at all, so there is no Dirac mass term.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (etaZ etaZ_cast minkowskiSignZ sum_etaZ_mul
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. The covariant Pauli matrices

-/

/-- The Pauli matrices with the vector index lowered by the Minkowski metric. -/
def pauliLower (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (PauliMatrix.pauliSelfAdjoint' μ).1

/-- The covariant Pauli matrices are the basis vectors of `PauliMatrix.pauliBasis'`. -/
lemma pauliBasis'_coe (μ : Fin 1 ⊕ Fin 3) :
    (PauliMatrix.pauliBasis' μ).1 = pauliLower μ := by
  rw [PauliMatrix.pauliBasis', Module.Basis.coe_mk, pauliLower]

/-- Lowering the vector index multiplies by the Minkowski sign. -/
lemma pauliLower_eq_smul (μ : Fin 1 ⊕ Fin 3) :
    pauliLower μ = ((minkowskiSignZ μ : ℤ) : ℂ) • PauliMatrix.pauliMatrix μ := by
  rcases μ with μ | μ <;> fin_cases μ <;>
    simp [pauliLower, PauliMatrix.pauliSelfAdjoint', minkowskiSignZ]

/-- The conjugate Pauli matrices, the transposes of the covariant ones. These are the
  matrices `σ̄_μ` carrying two dual spinor indices. -/
def pauliBar (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (pauliLower μ)ᵀ

/-- The Fierz completeness relation for the covariant Pauli matrices: they form a basis
  of the two by two matrices, with the trace pairing as the duality. -/
lemma sum_pauliLower_mul_pauliLower (α α' β β' : Fin 2) :
    ∑ ρ : Fin 1 ⊕ Fin 3, pauliLower ρ β' β * pauliLower ρ α α'
      = 2 * ((if α = β then 1 else 0) * (if α' = β' then 1 else 0)) := by
  fin_cases α <;> fin_cases α' <;> fin_cases β <;> fin_cases β' <;>
    simp [pauliLower, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Fintype.sum_sum_type, Fin.sum_univ_three] <;>
    norm_num [Complex.ext_iff]

/-- The intertwining property of the covariant Pauli matrices, in components: sandwiching
  `σ_μ` between `g` and `gᴴ` mixes the covariant Pauli matrices by the column of the
  Lorentz matrix of `g`. This is `SL2C.toSelfAdjointMap_basis` read entrywise. -/
lemma sum_pauliLower_mul_sl2c (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (β β' : Fin 2) :
    ∑ p : Fin 2 × Fin 2, pauliLower μ p.1 p.2 * (g.1 β p.1 * star (g.1 β' p.2))
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * pauliLower ν β β' := by
  have h := congrArg (fun A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) => A.1 β β')
    (SL2C.toSelfAdjointMap_basis (M := g) μ)
  simp only [SL2C.toSelfAdjointMap_apply_coe, AddSubmonoidClass.coe_finsetSum,
    Matrix.sum_apply, selfAdjoint.val_smul, Matrix.smul_apply, Complex.real_smul,
    pauliBasis'_coe] at h
  rw [← h, Matrix.mul_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun p₂ _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p₁ _ => by
    rw [Matrix.conjTranspose_apply]
    ring

/-!

## B. Vector-Weyl families and the span of their components

-/

/-- A sum over families of two four-vector indices is a double sum. -/
lemma sum_pi_fin_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, f ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3), f ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- A family `T` of elements of `B`, indexed by one four-vector index, one left-handed
  and one right-handed Weyl index, transforms as a tensor `T^{μ α α'}` under the
  representation `repLorentz` of `SL(2,ℂ)`: the vector index moves by the Lorentz matrix
  of the `SL(2,ℂ)` element, the left index by the matrix itself and the right index by
  its complex conjugate. -/
structure IsVectorLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
      ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * (g.1 a.1 l.1 * star (g.1 a.2 l.2))) • T (ν, a)

namespace IsVectorLeftRightWeyl
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
  (hT : IsVectorLeftRightWeyl B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsVectorLeftRightWeyl B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The span of the components is exactly the set of linear combinations of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → ℂ, y = ∑ d, c d • T d)
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

/-- The Pauli contraction `σ_μ^{α α'} T^μ_{α α'}`, the kinetic-term contraction of a
  four-vector index against a pair of opposite-chirality Weyl indices. -/
noncomputable def pauliContraction : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2,
    PauliMatrix.pauliMatrix μ a.1 a.2 • T (μ, a)

end IsVectorLeftRightWeyl

/-!

## C. The reduction to a pair of four-vector indices

-/

namespace IsVectorLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
  (hT : IsVectorLeftRightWeyl B repLorentz T)

/-- The family of two four-vector indices obtained by contracting the Weyl pair of `T`
  against the covariant Pauli matrices. -/
noncomputable def vectorPair : (Fin 2 → Fin 1 ⊕ Fin 3) → B :=
  fun d => ∑ a : Fin 2 × Fin 2, pauliLower (d 1) a.1 a.2 • T (d 0, a)

include hT in
/-- The Pauli contraction of the Weyl pair carries the two spinor indices into a second
  four-vector index: the resulting family is a bi-Lorentz tensor. -/
lemma isBiLorentz_vectorPair : IsBiLorentz B repLorentz (vectorPair (T := T)) where
  repLorentz_T g l := by
    have hstep : ∀ p : Fin 2 × Fin 2,
        pauliLower (l 1) p.1 p.2 • repLorentz g (T (l 0, p))
          = ∑ ν : Fin 1 ⊕ Fin 3, ∑ q : Fin 2 × Fin 2,
              (pauliLower (l 1) p.1 p.2 * ((((SL2C.toLorentzGroup g).1 ν (l 0) : ℝ) : ℂ)
                * (g.1 q.1 p.1 * star (g.1 q.2 p.2)))) • T (ν, q) := by
      intro p
      rw [hT.repLorentz_T g (l 0) p, Finset.smul_sum]
      exact Finset.sum_congr rfl fun ν _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => smul_smul _ _ _
    calc repLorentz g (vectorPair (T := T) l)
        = ∑ p : Fin 2 × Fin 2,
            pauliLower (l 1) p.1 p.2 • repLorentz g (T (l 0, p)) := by
          simp only [vectorPair, map_sum, map_smul]
      _ = ∑ ν : Fin 1 ⊕ Fin 3, ∑ q : Fin 2 × Fin 2,
            (∑ p : Fin 2 × Fin 2, pauliLower (l 1) p.1 p.2
              * ((((SL2C.toLorentzGroup g).1 ν (l 0) : ℝ) : ℂ)
                * (g.1 q.1 p.1 * star (g.1 q.2 p.2)))) • T (ν, q) := by
          simp only [hstep]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => (Finset.sum_smul).symm
      _ = ∑ ν : Fin 1 ⊕ Fin 3, ∑ ρ : Fin 1 ⊕ Fin 3,
            ((((SL2C.toLorentzGroup g).1 ν (l 0) : ℝ) : ℂ)
              * (((SL2C.toLorentzGroup g).1 ρ (l 1) : ℝ) : ℂ))
              • vectorPair (T := T) ![ν, ρ] := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          have hinner : ∀ q : Fin 2 × Fin 2,
              (∑ p : Fin 2 × Fin 2, pauliLower (l 1) p.1 p.2
                * ((((SL2C.toLorentzGroup g).1 ν (l 0) : ℝ) : ℂ)
                  * (g.1 q.1 p.1 * star (g.1 q.2 p.2))))
                = (((SL2C.toLorentzGroup g).1 ν (l 0) : ℝ) : ℂ)
                  * ∑ ρ : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ρ (l 1) : ℝ) : ℂ)
                    * pauliLower ρ q.1 q.2 := by
            intro q
            rw [← sum_pauliLower_mul_sl2c g (l 1) q.1 q.2, Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by ring
          simp only [hinner]
          symm
          simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one,
            Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_smul, Finset.mul_sum]
          exact congrArg (· • T (ν, q)) (Finset.sum_congr rfl fun ρ _ => by ring)
      _ = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3,
            (∏ i : Fin 2, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ))
              • vectorPair (T := T) a := by
          rw [sum_pi_fin_two]
          refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
          simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every component of the reduced family lies in the span of the components of `T`. -/
lemma vectorPair_mem_span (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    vectorPair (T := T) d ∈ hT.span :=
  sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem (d 0, a) (Submodule.mem_span_singleton_self _))

/-- The reduction is invertible: by the Fierz completeness relation each component of
  `T` is recovered from the reduced family. -/
lemma eq_sum_vectorPair (μ : Fin 1 ⊕ Fin 3) (b : Fin 2 × Fin 2) :
    T (μ, b) = ∑ ρ : Fin 1 ⊕ Fin 3,
      ((2 : ℂ)⁻¹ * pauliLower ρ b.2 b.1) • vectorPair (T := T) ![μ, ρ] := by
  calc T (μ, b) = ∑ a : Fin 2 × Fin 2,
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then 1 else 0)) • T (μ, a) := by
        rw [Fintype.sum_prod_type]
        simp [ite_smul, Finset.sum_ite_eq']
    _ = ∑ a : Fin 2 × Fin 2, (∑ ρ : Fin 1 ⊕ Fin 3,
          (2 : ℂ)⁻¹ * pauliLower ρ b.2 b.1 * pauliLower ρ a.1 a.2) • T (μ, a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [show (∑ ρ : Fin 1 ⊕ Fin 3,
              (2 : ℂ)⁻¹ * pauliLower ρ b.2 b.1 * pauliLower ρ a.1 a.2)
            = (2 : ℂ)⁻¹ * ∑ ρ : Fin 1 ⊕ Fin 3,
              pauliLower ρ b.2 b.1 * pauliLower ρ a.1 a.2 from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => (mul_assoc _ _ _),
          sum_pauliLower_mul_pauliLower a.1 a.2 b.1 b.2]
        field_simp
    _ = _ := by
        simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul

omit hT in
/-- Every component of `T` lies in the span of the components of the reduced family. -/
lemma mem_span_vectorPair (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    T d ∈ ⨆ e, ℂ ∙ vectorPair (T := T) e := by
  rw [show T d = T (d.1, d.2) from rfl, eq_sum_vectorPair (T := T) d.1 d.2]
  exact sum_mem fun ρ _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem _ (Submodule.mem_span_singleton_self _))

include hT in
/-- The reduction does not change the span of the components. -/
lemma iSup_span_vectorPair : (⨆ e, ℂ ∙ vectorPair (T := T) e) = hT.span := by
  refine le_antisymm (iSup_le fun e => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.vectorPair_mem_span e
  · rw [Submodule.span_singleton_le_iff_mem]
    exact mem_span_vectorPair (T := T) d

/-- The metric trace of the reduced family is exactly the Pauli contraction of `T`: the
  two lowerings of the vector index cancel, so no sign and no scalar appear. -/
lemma metricContraction_vectorPair :
    IsBiLorentz.metricContraction (T := vectorPair (T := T)) = pauliContraction (T := T) := by
  rw [IsBiLorentz.metricContraction, sum_pi_fin_two, pauliContraction]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single ν (fun ρ _ hρ => ?_) (fun hν => absurd (Finset.mem_univ ν) hν)]
  · simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [pauliLower_eq_smul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    rcases ν with ν | ν <;> fin_cases ν <;> norm_num [etaZ, minkowskiSignZ]
  · rw [show etaZ (![ν, ρ] 0) (![ν, ρ] 1) = 0 from by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [etaZ, Ne.symm hρ]]
    simp

/-!

## D. The classification of the Lorentz invariants

-/

include hT in
/-- The Pauli contraction really is a Lorentz invariant: this is the metric invariance
  `Λ η Λᵀ = η` read through the reduction of section C. -/
lemma repLorentz_pauliContraction (g : SL(2,ℂ)) :
    repLorentz g (pauliContraction (T := T)) = pauliContraction (T := T) := by
  have hV := hT.isBiLorentz_vectorPair
  have hstep : ∀ d : Fin 2 → Fin 1 ⊕ Fin 3,
      repLorentz g (((etaZ (d 0) (d 1) : ℤ) : ℂ) • vectorPair (T := T) d)
        = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3,
            (((etaZ (d 0) (d 1) : ℤ) : ℂ)
              * ∏ i : Fin 2, (((SL2C.toLorentzGroup g).1 (a i) (d i) : ℝ) : ℂ))
              • vectorPair (T := T) a := by
    intro d
    rw [map_smul, hV.repLorentz_T g d, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  rw [← metricContraction_vectorPair (T := T), IsBiLorentz.metricContraction, map_sum]
  calc ∑ d : Fin 2 → Fin 1 ⊕ Fin 3,
        repLorentz g (((etaZ (d 0) (d 1) : ℤ) : ℂ) • vectorPair (T := T) d)
      = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3, (∑ d : Fin 2 → Fin 1 ⊕ Fin 3,
          ((etaZ (d 0) (d 1) : ℤ) : ℂ)
            * ∏ i : Fin 2, (((SL2C.toLorentzGroup g).1 (a i) (d i) : ℝ) : ℂ))
          • vectorPair (T := T) a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3,
          ((etaZ (a 0) (a 1) : ℤ) : ℂ) • vectorPair (T := T) a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [sum_pi_fin_two]
        rw [← sum_etaZ_mul (SL2C.toLorentzGroup g) (a 0) (a 1)]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

include hT in
/-- The classification of the Lorentz invariants: a four-vector index together with a
  left-handed and a right-handed Weyl index admit the single invariant contraction
  against the Pauli matrices, so every element of the span of the components fixed by the
  Lorentz group is a scalar multiple of `pauliContraction`. -/
theorem exists_smul_pauliContraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • pauliContraction (T := T) := by
  have hV := hT.isBiLorentz_vectorPair
  have hx' : x ∈ hV.span := by
    rw [IsBiLorentz.span, hT.iSup_span_vectorPair]
    exact hx
  obtain ⟨a, ha⟩ := hV.exists_smul_metricContraction_of_invariant hx' hinv
  exact ⟨a, by rwa [metricContraction_vectorPair] at ha⟩

include hT in
/-- The classification of the Lorentz invariants modulo a stable submodule: an element of
  the span of the components together with a Lorentz-stable submodule `S`, fixed by the
  Lorentz group, is a multiple of the Pauli contraction up to an error in `S`. -/
lemma exists_smul_pauliContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • pauliContraction (T := T) + y := by
  have hV := hT.isBiLorentz_vectorPair
  have hx' : x ∈ hV.span ⊔ S := by
    rw [IsBiLorentz.span, hT.iSup_span_vectorPair]
    exact hx
  obtain ⟨a, y, hy, ha⟩ :=
    hV.exists_smul_metricContraction_of_invariant_subset S hS hx' hinv
  exact ⟨a, y, hy, by rwa [metricContraction_vectorPair] at ha⟩

end IsVectorLeftRightWeyl

/-!

## E. The Pauli tensor as the model example

The tensor product of the complex four-vector representation with the two Weyl
representations carries exactly this index law on the products of basis vectors, and the
Pauli contraction of that family is the repo's `PauliMatrix.asTensor`. So the classifier
is not vacuous, and on the model family the invariant line is spanned by a tensor already
known to be nonzero.


-/

open Fermion in
/-- The tensor product of the complex four-vector representation with the left-handed and
  the right-handed Weyl representations, on the products of basis vectors, is the basic
  example of a family with this index law. -/
lemma isVectorLeftRightWeyl_pauli :
    IsVectorLeftRightWeyl (ContrℂModule ⊗[ℂ] (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl))
      (ContrℂModule.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep))
      (fun d => complexContrBasis d.1 ⊗ₜ[ℂ]
        (LeftHandedWeyl.basis d.2.1 ⊗ₜ[ℂ] RightHandedWeyl.basis d.2.2)) where
  repLorentz_T g μ l := by
    have hC : (ContrℂModule.SL2CRep g) (complexContrBasis μ)
        = ∑ ν, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • complexContrBasis ν := by
      rw [SL2CRep_ρ_basis]
      exact Finset.sum_congr rfl fun ν _ => (algebraMap_smul ℂ _ _).symm
    have hR : (RightHandedWeyl.rep g) (RightHandedWeyl.basis l.2)
        = ∑ y, star (g.1 y l.2) • RightHandedWeyl.basis y := by
      rw [RightHandedWeyl.rep_apply_basis]
      exact Finset.sum_congr rfl fun y _ => by rw [Matrix.map_apply]
    have hinner : (∑ x, g.1 x l.1 • LeftHandedWeyl.basis x) ⊗ₜ[ℂ]
          (∑ y, star (g.1 y l.2) • RightHandedWeyl.basis y)
        = ∑ a : Fin 2 × Fin 2, (g.1 a.1 l.1 * star (g.1 a.2 l.2))
            • (LeftHandedWeyl.basis a.1 ⊗ₜ[ℂ] RightHandedWeyl.basis a.2) := by
      rw [TensorProduct.sum_tmul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, hC, hR, LeftHandedWeyl.rep_apply_basis, hinner,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
      module

open PauliMatrix Fermion in
/-- The Pauli contraction of the model family is the Pauli tensor `σ^μ{}^α{}^{α'}` of
  `PauliMatrix.asTensor`: the classification of section D says that this tensor spans
  the invariants, so the invariant space really is one dimensional here. -/
lemma pauliContraction_pauli :
    IsVectorLeftRightWeyl.pauliContraction
        (T := fun d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 => complexContrBasis d.1 ⊗ₜ[ℂ]
          (LeftHandedWeyl.basis d.2.1 ⊗ₜ[ℂ] RightHandedWeyl.basis d.2.2))
      = PauliMatrix.asTensor := by
  rw [IsVectorLeftRightWeyl.pauliContraction, asTensor_expand]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.sum_univ_three, Fintype.sum_prod_type, Fin.sum_univ_two,
    pauliMatrix, Matrix.one_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  module

/-!

## F. Dual Weyl indices and the `ε` re-index

-/

/-- A family `T` of elements of `B`, indexed by one dual left-handed and one dual
  right-handed Weyl index, transforms as a tensor `T_{α α'}` under `repLorentz`: the
  undotted index carries the contragredient matrix and the dotted one its complex
  conjugate. -/
structure IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2) • T a

/-- A family `T` of elements of `B`, indexed by one four-vector index, one dual
  left-handed and one dual right-handed Weyl index, transforms as a tensor
  `T^μ{}_{α α'}` under `repLorentz`. The vector index still carries the plain Lorentz
  matrix: in the Standard Model it is a derivative slot, and only the value index of a
  symbol is dualised. -/
structure IsVectorDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
      ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)

open Fermion in
/-- The tensor product of the dual left-handed and the dual right-handed Weyl
  representations, on the products of basis vectors, is the basic example of a family
  with the mixed contragredient index law. -/
lemma isDualLeftRightWeyl_dualWeyl :
    IsDualLeftRightWeyl (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl)
      (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep)
      (fun l => DualLeftHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualLeftHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

/-- The entries of the symplectic form are real. -/
lemma star_epsilon_apply (l k : Fin 2) : star (epsilon.1 l k) = epsilon.1 l k := by
  fin_cases l <;> fin_cases k <;> simp [SL2C.epsilon_coe]

/-- The conjugate single-index form of the symplectic identity: moving a conjugate
  contragredient factor across `ε` turns it into a conjugate fundamental factor. -/
lemma sum_epsilon_mul_inv_conjTranspose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᴴ a k
      = ∑ b : Fin 2, star (g.1 b l) * epsilon.1 b a := by
  have h := congrArg star (sum_epsilon_mul_inv_transpose g l a)
  simp only [star_sum, star_mul', star_epsilon_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- The mixed two-index form of the symplectic identity, obtained from the plain and the
  conjugate single-index forms by factorising each sum over the two slots. -/
lemma sum_mixedEpsilon_mul_inv (g : SL(2,ℂ)) (l a : Fin 2 × Fin 2) :
    ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
  have hL : (∑ k₁, epsilon.1 l.1 k₁ * (g.1⁻¹)ᵀ a.1 k₁)
      * (∑ k₂, epsilon.1 l.2 k₂ * (g.1⁻¹)ᴴ a.2 k₂)
      = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
  have hR : (∑ b₁, g.1 b₁ l.1 * epsilon.1 b₁ a.1)
      * (∑ b₂, star (g.1 b₂ l.2) * epsilon.1 b₂ a.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
  rw [← hL, ← hR, sum_epsilon_mul_inv_transpose, sum_epsilon_mul_inv_conjTranspose]

/-- The `ε` re-index turns a family with the mixed contragredient index law into a family
  with the mixed fundamental index law, for the very same representation. -/
lemma IsDualLeftRightWeyl.isLeftRightWeyl_epsReindex {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) :
    IsLeftRightWeyl B repLorentz (epsReindex T) where
  repLorentz_T g l := by
    have hstep : ∀ k : Fin 2 × Fin 2,
        (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • repLorentz g (T k)
          = ∑ a : Fin 2 × Fin 2, ((epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
              * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2)) • T a := by
      intro k
      rw [hT.repLorentz_T, Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
    calc repLorentz g (epsReindex T l)
        = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
            • repLorentz g (T k) := by
          simp only [epsReindex, map_sum, map_smul]
      _ = ∑ a : Fin 2 × Fin 2, (∑ k : Fin 2 × Fin 2,
            (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
              * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2)) • T a := by
          simp only [hstep]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
      _ = ∑ a : Fin 2 × Fin 2, (∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
            * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2)) • T a :=
          Finset.sum_congr rfl fun a _ => by rw [sum_mixedEpsilon_mul_inv]
      _ = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2)) • epsReindex T b := by
          symm
          simp only [epsReindex, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm

/-!

## G. The `ε` re-index of a vector-Weyl family

-/

/-- Conjugating a Pauli matrix by the symplectic form on both spinor slots produces the
  conjugate Pauli matrix of the same vector index. -/
lemma sum_pauliMatrix_mul_epsilon (μ : Fin 1 ⊕ Fin 3) (k₁ k₂ : Fin 2) :
    ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliMatrix μ a.1 a.2
        * (epsilon.1 a.1 k₁ * epsilon.1 a.2 k₂) = pauliBar μ k₁ k₂ := by
  rcases μ with μ | μ <;> fin_cases μ <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, PauliMatrix.pauliMatrix,
      pauliBar, pauliLower, PauliMatrix.pauliSelfAdjoint', SL2C.epsilon_coe]

/-- The `ε` re-index of a family carrying a four-vector index and a Weyl pair: the
  vector index is left alone and both spinor slots are transported through the
  symplectic form. -/
noncomputable def vectorEpsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B :=
  fun d => ∑ k : Fin 2 × Fin 2, (epsilon.1 d.2.1 k.1 * epsilon.1 d.2.2 k.2) • T (d.1, k)

section VectorReindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)

/-- At a fixed vector index the re-index is the `ε` re-index of the Weyl pair. -/
lemma vectorEpsReindex_eq_epsReindex (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) :
    vectorEpsReindex T (μ, l) = epsReindex (fun k => T (μ, k)) l := rfl

/-- The re-index is an involution, slot by slot. -/
lemma vectorEpsReindex_vectorEpsReindex :
    vectorEpsReindex (vectorEpsReindex T) = T := by
  funext d
  obtain ⟨μ, l⟩ := d
  have h : (fun k => vectorEpsReindex T (μ, k)) = epsReindex (fun k => T (μ, k)) := rfl
  rw [vectorEpsReindex_eq_epsReindex, h, epsReindex_epsReindex]

/-- Every re-indexed component lies in the span of the original components. -/
lemma vectorEpsReindex_mem_iSup (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    vectorEpsReindex T d ∈ ⨆ e, ℂ ∙ T e :=
  sum_mem fun k _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem (d.1, k) (Submodule.mem_span_singleton_self _))

/-- The re-index does not change the span of the components. -/
lemma iSup_span_vectorEpsReindex :
    (⨆ d, ℂ ∙ vectorEpsReindex T d) = ⨆ d, ℂ ∙ T d := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact vectorEpsReindex_mem_iSup T d
  · rw [Submodule.span_singleton_le_iff_mem]
    have h : T d = vectorEpsReindex (vectorEpsReindex T) d := by
      rw [vectorEpsReindex_vectorEpsReindex]
    rw [h]
    exact vectorEpsReindex_mem_iSup (vectorEpsReindex T) d

end VectorReindex

namespace IsVectorDualLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The conjugate Pauli contraction `σ̄_μ^{α' α} T^μ{}_{α α'}`, the kinetic-term
  contraction of a four-vector index against a pair of dual opposite-chirality Weyl
  indices. -/
noncomputable def pauliBarContraction : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2, pauliBar μ a.1 a.2 • T (μ, a)

/-- The `ε` re-index turns a family with the mixed contragredient index law into a family
  with the mixed fundamental index law, for the very same representation. -/
lemma isVectorLeftRightWeyl_vectorEpsReindex
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) :
    IsVectorLeftRightWeyl B repLorentz (vectorEpsReindex T) where
  repLorentz_T g μ l := by
    have hstep : ∀ k : Fin 2 × Fin 2,
        (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • repLorentz g (T (μ, k))
          = ∑ ν : Fin 1 ⊕ Fin 3, ∑ b : Fin 2 × Fin 2,
              ((epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
                * ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
                  * ((g.1⁻¹)ᵀ b.1 k.1 * (g.1⁻¹)ᴴ b.2 k.2))) • T (ν, b) := by
      intro k
      rw [hT.repLorentz_T g μ k, Finset.smul_sum]
      exact Finset.sum_congr rfl fun ν _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
    calc repLorentz g (vectorEpsReindex T (μ, l))
        = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
            • repLorentz g (T (μ, k)) := by
          simp only [vectorEpsReindex, map_sum, map_smul]
      _ = ∑ ν : Fin 1 ⊕ Fin 3, ∑ b : Fin 2 × Fin 2, (∑ k : Fin 2 × Fin 2,
            (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
              * ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
                * ((g.1⁻¹)ᵀ b.1 k.1 * (g.1⁻¹)ᴴ b.2 k.2))) • T (ν, b) := by
          simp only [hstep]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.sum_smul).symm
      _ = ∑ ν : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2,
            ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
              * (g.1 a.1 l.1 * star (g.1 a.2 l.2))) • vectorEpsReindex T (ν, a) := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          have hinner : ∀ b : Fin 2 × Fin 2,
              (∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
                * ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
                  * ((g.1⁻¹)ᵀ b.1 k.1 * (g.1⁻¹)ᴴ b.2 k.2)))
                = (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
                  * ∑ a : Fin 2 × Fin 2, (g.1 a.1 l.1 * star (g.1 a.2 l.2))
                    * (epsilon.1 a.1 b.1 * epsilon.1 a.2 b.2) := by
            intro b
            rw [← sum_mixedEpsilon_mul_inv g l b, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
          simp only [hinner]
          symm
          simp only [vectorEpsReindex, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_smul, Finset.mul_sum]
          exact congrArg (· • T (ν, b)) (Finset.sum_congr rfl fun a _ => by ring)

/-- The `ε` re-index carries the Pauli contraction of the re-indexed family to the
  conjugate Pauli contraction of the original one, with neither a sign nor a scalar
  appearing. -/
lemma pauliContraction_vectorEpsReindex :
    IsVectorLeftRightWeyl.pauliContraction (T := vectorEpsReindex T)
      = pauliBarContraction (T := T) := by
  rw [IsVectorLeftRightWeyl.pauliContraction, pauliBarContraction]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [vectorEpsReindex, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, ← sum_pauliMatrix_mul_epsilon μ k.1 k.2]

end IsVectorDualLeftRightWeyl

/-!

## H. The classification of the invariants of the dual families

-/

section DualClassification

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The classification of the Lorentz invariants of a family with the mixed
  contragredient index law: there is no invariant contraction of a dual left-handed
  against a dual right-handed Weyl index, so every element of the span of the components
  fixed by the Lorentz group is zero. This is the absence of a Dirac mass term. -/
theorem IsDualLeftRightWeyl.eq_zero_of_invariant {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  have hT' := hT.isLeftRightWeyl_epsReindex
  have hx' : x ∈ hT'.span := by
    rw [IsLeftRightWeyl.span, iSup_span_epsReindex]
    exact hx
  exact hT'.eq_zero_of_invariant hx' hinv

/-- The classification of the Lorentz invariants of a family with the mixed
  contragredient index law, modulo a Lorentz-stable submodule `S`: such an invariant
  already lies in `S`. -/
theorem IsDualLeftRightWeyl.mem_of_invariant_of_mem_sup {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ (⨆ d, ℂ ∙ T d) ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT' := hT.isLeftRightWeyl_epsReindex
  have hx' : x ∈ hT'.span ⊔ S := by
    rw [IsLeftRightWeyl.span, iSup_span_epsReindex]
    exact hx
  exact hT'.mem_of_invariant_of_mem_sup S hS hx' hinv

namespace IsVectorDualLeftRightWeyl

variable {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The conjugate Pauli contraction of a family with the mixed contragredient index law
  is Lorentz invariant. -/
lemma repLorentz_pauliBarContraction (hT : IsVectorDualLeftRightWeyl B repLorentz T)
    (g : SL(2,ℂ)) :
    repLorentz g (pauliBarContraction (T := T)) = pauliBarContraction (T := T) := by
  have h := hT.isVectorLeftRightWeyl_vectorEpsReindex.repLorentz_pauliContraction g
  rwa [pauliContraction_vectorEpsReindex] at h

/-- The classification of the Lorentz invariants of a family with the mixed
  contragredient index law: every element of the span of the components fixed by the
  Lorentz group is a scalar multiple of the conjugate Pauli contraction of that family.
  This is the kinetic term of a Weyl fermion. -/
theorem exists_smul_pauliBarContraction_of_invariant
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • pauliBarContraction (T := T) := by
  have hT' := hT.isVectorLeftRightWeyl_vectorEpsReindex
  have hx' : x ∈ hT'.span := by
    rw [IsVectorLeftRightWeyl.span, iSup_span_vectorEpsReindex]
    exact hx
  obtain ⟨a, ha⟩ := hT'.exists_smul_pauliContraction_of_invariant hx' hinv
  exact ⟨a, by rwa [pauliContraction_vectorEpsReindex] at ha⟩

/-- The classification of the Lorentz invariants of a family with the mixed
  contragredient index law, modulo a Lorentz-stable submodule `S`. -/
theorem exists_smul_pauliBarContraction_of_invariant_subset
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ (⨆ d, ℂ ∙ T d) ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • pauliBarContraction (T := T) + y := by
  have hT' := hT.isVectorLeftRightWeyl_vectorEpsReindex
  have hx' : x ∈ hT'.span ⊔ S := by
    rw [IsVectorLeftRightWeyl.span, iSup_span_vectorEpsReindex]
    exact hx
  obtain ⟨a, y, hy, ha⟩ :=
    hT'.exists_smul_pauliContraction_of_invariant_subset S hS hx' hinv
  exact ⟨a, y, hy, by rwa [pauliContraction_vectorEpsReindex] at ha⟩

end IsVectorDualLeftRightWeyl

end DualClassification

end Lorentz

