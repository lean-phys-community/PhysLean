/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.LinearMaps
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Cases
/-!
# Anomaly cancellation conditions

## i. Overview

Anomaly cancellation conditions (ACCs) are consistency conditions which arise
in gauge field theories. They correspond to a set of homogeneous diophantine equations
in the rational charges assigned to fermions under `u(1)` contributions to the gauge group.

These formally arise from triangle Feynman diagrams, but can otherwise be got from
index theorems.

## ii. Key results

There are four different types related to the underlying structure of
the ACCs:
- `ACCSystemCharges`: the structure carrying the number of charges present.
- `ACCSystemLinear`: the structure extending `ACCSystemCharges` with linear anomaly cancellation
  conditions.
- `ACCSystemQuad`: the structure extending `ACCSystemLinear` with quadratic anomaly cancellation
  conditions.
- `ACCSystem`: the structure extending `ACCSystemQuad` with the cubic anomaly cancellation
  condition.

Related to these are the different types of spaces of charges:
- `Charges`: the module of all possible charge allocations.
- `LinSols`: the module of solutions to the linear ACCs.
- `QuadSols`: the solutions to the linear and quadratic ACCs.
- `Sols`: the solutions to the full ACCs.

## iii. Table of contents

- A. The module of charges
  - A.1. A constructor for `ACCSystemCharges`
- B. The module of charges
  - B.1. The `ℚ`-module structure on the type `Charges`
  - B.2. The finiteness of the `ℚ`-module structure on `Charges`
- C. The linear anomaly cancellation conditions
- D. The module of solutions to the linear ACCs
  - D.1. Extensionality of solutions to the linear ACCs
  - D.2. Module structure on the solutions to the linear ACCs
  - D.3. Embedding of the solutions to the linear ACCs into the module of charges
- E. The quadratic anomaly cancellation conditions
- F. The solutions to the quadratic and linear anomaly cancellation conditions
  - F.1. Extensionality of solutions to the quadratic and linear ACCs
  - F.2. MulAction of rationals on the solutions to the quadratic and linear ACCs
  - F.3. Embeddings of quadratic solutions into linear solutions
  - F.4. Embeddings of solutions to linear ACCs into quadratic solutions when no quadratics
  - F.5. Embeddings of quadratic solutions into all charges
- G. The full anomaly cancellation conditions
- H. The solutions to the full anomaly cancellation conditions
  - H.1. Extensionality of solutions to the ACCs
  - H.2. The `IsSolution` predicate
  - H.3. MulAction of `ℚ` on the solutions to the ACCs
  - H.4. Embeddings of solutions to the ACCs into quadratic solutions
  - H.5. Embeddings of solutions to the ACCs into linear solutions
  - H.6. Embeddings of solutions to the ACCs into charges
- I. Morphisms between ACC systems
  - I.1. Composition of morphisms between ACC systems
- J. Open TODO items

## iv. References

Some references on anomaly cancellation conditions are:
- Alvarez-Gaume, L. and Ginsparg, P. H. (1985). The Structure of Gauge and
Gravitational Anomalies.
- Bilal, A. (2008). Lectures on Anomalies. arXiv preprint.
- Nash, C. (1991). Differential topology and quantum field theory. Elsevier.

-/

@[expose] public section

/-!

## A. The module of charges

We define the type `ACCSystemCharges`, this carries the charges
of the specification of the number of charges present in a theory.

For example for the standard model without right-handed neutrinos, this is `15` charges,
whilst with right handed neutrinos it is `18` charges.

We can think of `Fin χ.numberCharges` as an indexing type for
the representations present in the theory where `χ : ACCSystemCharges`.

-/

/-- A system of charges, specified by the number of charges. -/
structure ACCSystemCharges where
  /-- The number of charges. -/
  numberCharges : ℕ

/-!

### A.1. A constructor for `ACCSystemCharges`

We provide a constructor `ACCSystemChargesMk` for `ACCSystemCharges` given the number of charges.

-/

TODO "NCRC5" "Replace `ACCSystemChargesMk` with `⟨n⟩` notation everywhere. "
/--
  Creates an `ACCSystemCharges` object with the specified number of charges.
-/
def ACCSystemChargesMk (n : ℕ) : ACCSystemCharges where
  numberCharges := n

namespace ACCSystemCharges

/-!

## B. The module of charges

Given an `ACCSystemCharges` object `χ`, we define the type of charges
`χ.Charges` as functions from `Fin χ.numberCharges → ℚ`.

That is, for each representation in the theory, indexed by an element of `Fin χ.numberCharges`,
we assign a rational charge.

-/

/-- The charges as functions from `Fin χ.numberCharges → ℚ`. -/
def Charges (χ : ACCSystemCharges) : Type := Fin χ.numberCharges → ℚ

/-!

### B.1. The `ℚ`-module structure on the type `Charges`

The type `χ.Charges` has the structure of a module over the field `ℚ`.

-/

/--
  An instance to provide the necessary operations and properties for `charges` to form an additive
  commutative monoid.
-/
@[simps!]
instance chargesAddCommMonoid (χ : ACCSystemCharges) : AddCommMonoid χ.Charges :=
  Pi.addCommMonoid

/--
  An instance to provide the necessary operations and properties for `charges` to form a module
  over the field `ℚ`.
-/
@[simps!]
instance chargesModule (χ : ACCSystemCharges) : Module ℚ χ.Charges :=
  Pi.module _ _ _

instance ChargesAddCommGroup (χ : ACCSystemCharges) : AddCommGroup χ.Charges :=
  Module.addCommMonoidToAddCommGroup ℚ

/-!

### B.2. The finiteness of the `ℚ`-module structure on `Charges`

The type `χ.Charges` is a finite module.

-/

/-- The module `χ.Charges` over `ℚ` is finite. -/
instance (χ : ACCSystemCharges) : Module.Finite ℚ χ.Charges :=
  FiniteDimensional.finiteDimensional_pi ℚ

end ACCSystemCharges

/-!

## C. The linear anomaly cancellation conditions

We define the type `ACCSystemLinear` which extends `ACCSystemCharges` by adding
a finite number (determined by `numberLinear`) of linear equations in the rational charges.

-/

/-- The type of charges plus the linear ACCs. -/
structure ACCSystemLinear extends ACCSystemCharges where
  /-- The number of linear ACCs. -/
  numberLinear : ℕ
  /-- The linear ACCs. -/
  linearACCs : Fin numberLinear → (toACCSystemCharges.Charges →ₗ[ℚ] ℚ)

namespace ACCSystemLinear

/-!

## D. The module of solutions to the linear ACCs

We define the type `LinSols` of solutions to the linear ACCs.
That is the submodule of `χ.Charges` which satisfy all the linear ACCs.

-/

/-- The type of solutions to the linear ACCs. -/
structure LinSols (χ : ACCSystemLinear) where
  /-- The underlying charge. -/
  val : χ.1.Charges
  /-- The condition that the charge satisfies the linear ACCs. -/
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0

/-!

### D.1. Extensionality of solutions to the linear ACCs

We prove a lemma relating to the equality of two elements of `LinSols`.

-/

/-- Two solutions are equal if the underlying charges are equal. -/
@[ext]
lemma LinSols.ext {χ : ACCSystemLinear} {S T : χ.LinSols} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only

/-!

### D.2. Module structure on the solutions to the linear ACCs

we now give a module structure to `LinSols`.

-/

/-- An instance providing the operations and properties for `LinSols` to form an
  additive commutative monoid. -/
@[simps!]
instance linSolsAddCommMonoid (χ : ACCSystemLinear) :
    AddCommMonoid χ.LinSols where
  add S T := ⟨S.val + T.val, fun _ ↦ by simp [(χ.linearACCs _).map_add, S.linearSol _,
    T.linearSol _]⟩
  add_comm S T := LinSols.ext (χ.chargesAddCommMonoid.add_comm _ _)
  add_assoc S T L := LinSols.ext (χ.chargesAddCommMonoid.add_assoc _ _ _)
  zero := ⟨χ.chargesAddCommMonoid.zero, fun _ ↦ (χ.linearACCs _).map_zero⟩
  zero_add S := LinSols.ext (χ.chargesAddCommMonoid.zero_add _)
  add_zero S := LinSols.ext (χ.chargesAddCommMonoid.add_zero _)
  nsmul n S := ⟨n • S.val, fun _ ↦ by simp [S.linearSol _]⟩
  nsmul_zero n := by ext; simp only [zero_nsmul]; rfl
  nsmul_succ n S := LinSols.ext (χ.chargesAddCommMonoid.nsmul_succ _ _)

/-- An instance providing the operations and properties for `LinSols` to form a
  module over `ℚ`. -/
@[simps!]
instance linSolsModule (χ : ACCSystemLinear) : Module ℚ χ.LinSols where
  smul a S := ⟨a • S.val, fun _ ↦ by simp [(χ.linearACCs _).map_smul, S.linearSol _]⟩
  one_smul one_smul := LinSols.ext (χ.chargesModule.one_smul _)
  mul_smul a b S := LinSols.ext (χ.chargesModule.mul_smul _ _ _)
  smul_zero a := LinSols.ext (χ.chargesModule.smul_zero _)
  zero_smul S := LinSols.ext (χ.chargesModule.zero_smul _)
  smul_add a S T := LinSols.ext (χ.chargesModule.smul_add _ _ _)
  add_smul a b T:= LinSols.ext (χ.chargesModule.add_smul _ _ _)

instance linSolsAddCommGroup (χ : ACCSystemLinear) : AddCommGroup χ.LinSols :=
  Module.addCommMonoidToAddCommGroup ℚ

/-!

### D.3. Embedding of the solutions to the linear ACCs into the module of charges

We give the linear embedding of solutions to the linear ACCs `LinSols` into
the module of all `charges`.

-/

/-- The inclusion of `LinSols` into `charges`. -/
def linSolsIncl (χ : ACCSystemLinear) : χ.LinSols →ₗ[ℚ] χ.Charges where
  toFun S := S.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma linSolsIncl_injective (χ : ACCSystemLinear) :
    Function.Injective χ.linSolsIncl := fun _ _ h => LinSols.ext h

end ACCSystemLinear

/-!

## E. The quadratic anomaly cancellation conditions

We extend `ACCSystemLinear` to `ACCSystemQuad` by adding a finite number
(determined by `numberQuadratic`) of quadratic equations in the rational charges.

These quadratic anomaly cancellation conditions correspond to the interaction
of the `u(1)` part of the gauge group of interest with another abelian part.

-/

/-- The type of charges plus the linear ACCs plus the quadratic ACCs. -/
structure ACCSystemQuad extends ACCSystemLinear where
  /-- The number of quadratic ACCs. -/
  numberQuadratic : ℕ
  /-- The quadratic ACCs. -/
  quadraticACCs : Fin numberQuadratic → HomogeneousQuadratic toACCSystemCharges.Charges

namespace ACCSystemQuad

/-!

## F. The solutions to the quadratic and linear anomaly cancellation conditions

We define the type `QuadSols` of solutions to the linear and quadratic ACCs.

-/

/-- The type of solutions to the linear and quadratic ACCs. -/
structure QuadSols (χ : ACCSystemQuad) extends χ.LinSols where
  /-- The condition that the charge satisfies the quadratic ACCs. -/
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0

/-!

### F.1. Extensionality of solutions to the quadratic and linear ACCs

We prove a lemma relating to the equality of two elements of `QuadSols`.

-/

/-- Two `QuadSols` are equal if the underlying charges are equal. -/
@[ext]
lemma QuadSols.ext {χ : ACCSystemQuad} {S T : χ.QuadSols} (h : S.val = T.val) :
    S = T := by
  have h := ACCSystemLinear.LinSols.ext h
  cases' S
  simp_all only

/-!

### F.2. MulAction of rationals on the solutions to the quadratic and linear ACCs

The type `QuadSols` does not carry the structure of a module over `ℚ` as
the quadratic ACCs are not linear. However it does carry the structure of
a `MulAction` of `ℚ`.

-/
/-- An instance giving the properties and structures to define an action of `ℚ` on `QuadSols`. -/
instance quadSolsMulAction (χ : ACCSystemQuad) : MulAction ℚ χ.QuadSols where
  smul a S := ⟨a • S.toLinSols, fun _ ↦ by erw [(χ.quadraticACCs _).map_smul, S.quadSol _,
    mul_zero]⟩
  mul_smul a b S := QuadSols.ext (mul_smul _ _ _)
  one_smul S := QuadSols.ext (one_smul _ _)

/-!

### F.3. Embeddings of quadratic solutions into linear solutions

We give the equivariant of solutions to the quadratic and linear ACCs `QuadSols` into
the solutions to the linear ACCs `LinSols`.

-/

/-- The inclusion of quadratic solutions into linear solutions. -/
def quadSolsInclLinSols (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.LinSols where
  toFun := QuadSols.toLinSols
  map_smul' _ _ := rfl

lemma quadSolsInclLinSols_injective (χ : ACCSystemQuad) :
    Function.Injective χ.quadSolsInclLinSols := by
  intro S T h
  ext
  simpa [ACCSystemQuad.quadSolsInclLinSols] using
    congrArg (fun X => X.val) h

/-!

### F.4. Embeddings of solutions to linear ACCs into quadratic solutions when no quadratics

When there are no quadratic ACCs, the solutions to the linear ACCs embed into the solutions
to the quadratic and linear ACCs.

-/

/-- The inclusion of the linear solutions into the quadratic solutions, where there is
  no quadratic equations (i.e. no U(1)'s in the underlying gauge group). -/
def linSolsInclQuadSolsZero (χ : ACCSystemQuad) (h : χ.numberQuadratic = 0) :
    χ.LinSols →[ℚ] χ.QuadSols where
  toFun S := ⟨S, by intro i; rw [h] at i; exact Fin.elim0 i⟩
  map_smul' _ _ := rfl

/-!

### F.5. Embeddings of quadratic solutions into all charges

We give the equivariant embedding of solutions to the quadratic and linear ACCs `QuadSols` into
the module of all charges `Charges`.

-/

/-- The inclusion of quadratic solutions into all charges. -/
def quadSolsIncl (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.Charges :=
  MulActionHom.comp χ.linSolsIncl.toMulActionHom χ.quadSolsInclLinSols

lemma quadSolsIncl_injective (χ : ACCSystemQuad) :
    Function.Injective χ.quadSolsIncl := by
  intro S T h
  have h' : χ.quadSolsInclLinSols S = χ.quadSolsInclLinSols T := by
    apply ACCSystemLinear.linSolsIncl_injective (χ := χ.toACCSystemLinear)
    simpa [ACCSystemQuad.quadSolsIncl, MulActionHom.comp_apply] using h
  exact quadSolsInclLinSols_injective χ h'

end ACCSystemQuad

/-!

## G. The full anomaly cancellation conditions

We extend `ACCSystemQuad` to `ACCSystem` by adding the single cubic equation
in the rational charges. This corresponds to the `u(1)^3` anomaly.

-/

/--
The type of charges plus the anomaly cancellation conditions.

In many physical settings these conditions are derived formally from the gauge group and the
fermionic representations. They arise from triangle Feynman diagrams, and can also be obtained
using index-theoretic or characteristic-class constructions.

In this file, we take the resulting conditions as input data: linear, quadratic and cubic
homogeneous forms on the space of rational charges.
-/
structure ACCSystem extends ACCSystemQuad where
  /-- The cubic ACC. -/
  cubicACC : HomogeneousCubic toACCSystemCharges.Charges

namespace ACCSystem

/-!

## H. The solutions to the full anomaly cancellation conditions

We define the type `Sols` of solutions to the full ACCs.

-/

/-- The type of solutions to the anomaly cancellation conditions. -/
structure Sols (χ : ACCSystem) extends χ.QuadSols where
  /-- The condition that the charge satisfies the cubic ACC. -/
  cubicSol : χ.cubicACC val = 0

/-!

### H.1. Extensionality of solutions to the ACCs

We prove a lemma relating to the equality of two elements of `Sols`.

-/

/-- Two solutions are equal if the underlying charges are equal. -/
lemma Sols.ext {χ : ACCSystem} {S T : χ.Sols} (h : S.val = T.val) :
    S = T := by
  have h := ACCSystemQuad.QuadSols.ext h
  cases' S
  simp_all only

/-!

### H.2. The `IsSolution` predicate

we define a predicate on charges which is true if they correspond to a solution.

-/

/-- A charge `S` is a solution if it extends to a solution. -/
def IsSolution (χ : ACCSystem) (S : χ.Charges) : Prop :=
  ∃ (sol : χ.Sols), sol.val = S

/-!

### H.3. MulAction of `ℚ` on the solutions to the ACCs

Like with `QuadSols`, the type `Sols` does not carry the structure of a module over `ℚ`
as the cubic nor quadratic ACC is not linear. However it does carry the structure of
a `MulAction` of `ℚ`.

-/

/-- An instance giving the properties and structures to define an action of `ℚ` on `Sols`. -/
instance solsMulAction (χ : ACCSystem) : MulAction ℚ χ.Sols where
  smul a S := ⟨a • S.toQuadSols, by
    erw [(χ.cubicACC).map_smul, S.cubicSol]
    exact Rat.mul_zero (a ^ 3)⟩
  mul_smul a b S := Sols.ext (mul_smul _ _ _)
  one_smul S := Sols.ext (one_smul _ _)

/-!

### H.4. Embeddings of solutions to the ACCs into quadratic solutions

-/

/-- The inclusion of `Sols` into `QuadSols`. -/
def solsInclQuadSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.QuadSols where
  toFun := Sols.toQuadSols
  map_smul' _ _ := rfl

lemma solsInclQuadSols_injective (χ : ACCSystem) :
    Function.Injective χ.solsInclQuadSols := by
  intro S T h
  apply Sols.ext
  have hv : (χ.solsInclQuadSols S).val = (χ.solsInclQuadSols T).val :=
    congrArg (fun X => X.val) h
  simpa [ACCSystem.solsInclQuadSols] using hv

/-!

### H.5. Embeddings of solutions to the ACCs into linear solutions

-/
/-- The inclusion of `Sols` into `LinSols`. -/
def solsInclLinSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.LinSols :=
  MulActionHom.comp χ.quadSolsInclLinSols χ.solsInclQuadSols

lemma solsInclLinSols_injective (χ : ACCSystem) :
    Function.Injective χ.solsInclLinSols := by
  intro S T h
  have h' : χ.solsInclQuadSols S = χ.solsInclQuadSols T := by
    apply ACCSystemQuad.quadSolsInclLinSols_injective (χ := χ.toACCSystemQuad)
    simpa [ACCSystem.solsInclLinSols, MulActionHom.comp_apply] using h
  exact solsInclQuadSols_injective χ h'

/-!

### H.6. Embeddings of solutions to the ACCs into charges

-/

/-- The inclusion of `Sols` into `LinSols`. -/
def solsIncl (χ : ACCSystem) : χ.Sols →[ℚ] χ.Charges :=
  MulActionHom.comp χ.quadSolsIncl χ.solsInclQuadSols

lemma solsIncl_injective (χ : ACCSystem) :
    Function.Injective χ.solsIncl := by
  intro S T h
  have h' : χ.solsInclQuadSols S = χ.solsInclQuadSols T := by
    apply ACCSystemQuad.quadSolsIncl_injective (χ := χ.toACCSystemQuad)
    simpa [ACCSystem.solsIncl, MulActionHom.comp_apply] using h
  exact (solsInclQuadSols_injective χ) h'

/-!

## I. Morphisms between ACC systems

We define a morphisms between two `ACCSystem` objects.
as a linear map between their spaces of charges and a map between their spaces of solutions
such that mapping solutions and then including in the module of charges
is the same as including in the module of charges and then mapping charges.

-/

/-- The structure of a map between two ACCSystems. -/
structure Hom (χ η : ACCSystem) where
  /-- The linear map between vector spaces of charges. -/
  charges : χ.Charges →ₗ[ℚ] η.Charges
  /-- The map between solutions. -/
  anomalyFree : χ.Sols → η.Sols
  /-- The condition that the map commutes with the relevant inclusions. -/
  commute : charges ∘ χ.solsIncl = η.solsIncl ∘ anomalyFree

/-!

### I.1. Composition of morphisms between ACC systems

-/

/-- The definition of composition between two ACCSystems. -/
def Hom.comp {χ η ε : ACCSystem} (g : Hom η ε) (f : Hom χ η) : Hom χ ε where
  charges := LinearMap.comp g.charges f.charges
  anomalyFree := g.anomalyFree ∘ f.anomalyFree
  commute := by rw [LinearMap.coe_comp, Function.comp_assoc, f.commute,
    ← Function.comp_assoc, g.commute, Function.comp_assoc]

end ACCSystem

/-!

## J. Open TODO items

We give some open TODO items for future work.

One natural direction is to formalize how the anomaly cancellation conditions defining an
`ACCSystem` arise from gauge-theoretic data (a gauge group together with fermionic representations).
Physically these arise from triangle Feynman diagrams, and can also be described via index-theoretic
or characteristic-class constructions (e.g. through an anomaly polynomial). At present we do not
formalize this derivation in Lean, and instead take the resulting homogeneous forms as data.

(To view these you may need to go to the GitHub source code for the file.)

-/

TODO "6VZMW" "Anomaly cancellation conditions can be derived formally from the gauge group
  and fermionic representations using e.g. topological invariants. Include such a
  definition."

TODO "6VZM3" "Anomaly cancellation conditions can be defined using algebraic varieties.
  Link such an approach to the approach here."
