/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Adiabatic accessibility

## i. Overview

This module defines a thermodynamics interface for the abstract Lieb-Yngvason accessibility
foundation.

The primitive is a preorder `≺` of **adiabatic accessibility** between equilibrium
states: `X ≺ Y` means `Y` can be reached from `X` by an interaction with a device and a
weight, the device returning to its initial state while the weight may have moved in a
gravitational field (Lieb-Yngvason 1999, §II.A). From `≺` one reads off adiabatic
equivalence `X ≈ Y` (`X ≺ Y` and `Y ≺ X`) and strict accessibility `X ≺≺ Y` (`X ≺ Y`
but not `Y ≺ X`), the latter being the irreversible processes.

The eventual goal would be an entropy `S` with `X ≺ Y ⟺ S(X) ≤ S(Y)` on comparable states,
additive and extensive, unique up to affine rescaling `S ↦ aS + B` (`a > 0`).

The file is split into two classes:

* `ThermoSystemCore` contains the operational vocabulary: systems, their state
  spaces, composition, scaling, the zero system, and the primitive adiabatic-accessibility
  relation `≺`.
* `ThermoWorld` extends the core with the algebraic identities on systems, the
  accessibility axioms A1-A6, and the cast-coherence axioms needed because Lean
  distinguishes propositionally-equal state spaces that Lieb-Yngvason identify.

## ii. Key results

- `ThermoSystemCore` / `ThermoWorld` — the two-layer abstract interface.
- `Comparable`, `ComparisonHypothesis`, `GlobalComparisonHypothesis` — the comparability
  vocabulary. The comparison hypothesis is stated as a *hypothesis*, carried separately,
  never baked into the axioms (see §C).
- `StrictlyPrecedes` (`≺≺`) — irreversible accessibility.
- `thermo_le_refl`, `thermo_le_trans`, `thermo_equiv_refl`, `thermo_equiv_symm`,
  `calcTransThermoLe` — the preorder API exposing A1/A2 for calculation.

## iii. Table of contents

- A. Operational core (`ThermoSystemCore`)
- B. Lieb-Yngvason worlds (`ThermoWorld`)
  - B.1. System algebra
  - B.2. Accessibility axioms A1-A6
  - B.3. Coherence of casts
- C. Comparability
- D. Core API
- E. World API

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999) 1-96. Adiabatic accessibility and its
  operational definition, §II.A; the entropy principle, §II.B; the order axioms A1-A6 and
  the comparison hypothesis CH, §II.C.
- E.H. Lieb and J. Yngvason, *The Mathematical Structure of the Second Law of
  Thermodynamics*, Current Developments in Mathematics **2001** (2002) 89-129;
  arXiv:math-ph/0204007. A streamlined re-presentation of the same axiomatics.
-/

@[expose] public section

namespace Thermodynamics

universe u v

/-! ## A. Operational core

We first fix the operational vocabulary of thermodynamics with no axioms attached.
A `ThermoSystemCore` records, for each *system*, its space of equilibrium *states*,
together with the two ways of building new systems — composition `⊗` (placing two systems
side by side) and scaling `•` (taking a `t`-sized copy) — the zero system, and the
primitive adiabatic-accessibility relation `≺`. Separating this core from the axioms lets
later layers depend only on the vocabulary they actually use. -/

/-- The operational core of a thermodynamic accessibility structure.

A `ThermoSystemCore` records the state space indexed by each system, system composition,
system scaling, the zero system, and the primitive adiabatic-accessibility relation. -/
class ThermoSystemCore (System : Type u) where
  /-- The state space associated to a thermodynamic system. -/
  State : System → Type v
  /-- Composition of thermodynamic systems. -/
  comp : System → System → System
  /-- Extensive scaling of thermodynamic systems by a real parameter. -/
  scale : ℝ → System → System
  /-- Primitive adiabatic accessibility `X ≺ Y`: `Y` can be reached from `X` by an
  interaction with a device and a weight, the device returning to its initial state while
  the weight may change height. States may belong to different systems. -/
  le {Γ₁ Γ₂ : System} : State Γ₁ → State Γ₂ → Prop
  /-- The zero system. -/
  ZSystem : System
  /-- The zero system has a unique state. -/
  State_ZSystem_is_Unit : Unique (State ZSystem)
  /-- A state of a composed system is represented by a pair of states of the components. -/
  state_of_comp_equiv {Γ₁ Γ₂ : System} : State (comp Γ₁ Γ₂) ≃ (State Γ₁ × State Γ₂)
  /-- A state of a nonzero-scaled system is represented by a state of the original system. -/
  state_of_scale_equiv {t : ℝ} (ht : t ≠ 0) {Γ : System} : State (scale t Γ) ≃ State Γ

/-! ## B. Lieb-Yngvason worlds

A `ThermoWorld` extends the core with the assumptions Lieb-Yngvason place on `≺`. These
fall into three groups: the algebraic identities making composition an associative,
commutative operation on which scaling acts compatibly; the six accessibility
axioms A1-A6; and coherence axioms relating states across *equal* systems. The last
group has no Lieb-Yngvason axiom number: the paper treats identities like
`(Γ₁ ⊗ Γ₂) = (Γ₂ ⊗ Γ₁)` as strict equalities of state spaces and uses them silently, but in
Lean equal systems yield state spaces that are only propositionally equal, so each identity
is paired with a statement that transporting a state along it lands on an
adiabatically-equivalent state.

The fields are assumptions of the abstract world. -/

/--
This extends `ThermoSystemCore` with the structural equalities, accessibility axioms A1-A6,
and coherence axioms needed to reason about casts induced by equalities of systems. -/
class ThermoWorld (System : Type u) extends ThermoSystemCore System where
  /-- Scaling by zero gives the zero system. -/
  scale_zero_is_ZSystem (Γ : System) : scale 0 Γ = ZSystem

  /-- Composition of systems is associative, up to equality of systems. -/
  comp_assoc (Γ₁ Γ₂ Γ₃ : System) : comp (comp Γ₁ Γ₂) Γ₃ = comp Γ₁ (comp Γ₂ Γ₃)
  /-- Composition of systems is commutative, up to equality of systems. -/
  comp_comm (Γ₁ Γ₂ : System) : comp Γ₁ Γ₂ = comp Γ₂ Γ₁
  /-- Scaling distributes over composition of systems. -/
  scale_distrib_comp (t : ℝ) (Γ₁ Γ₂ : System) :
    scale t (comp Γ₁ Γ₂) = comp (scale t Γ₁) (scale t Γ₂)
  /-- Successive scalings multiply their scale factors. -/
  smul_smul (t s : ℝ) (Γ : System) : scale (t * s) Γ = scale t (scale s Γ)
  /-- Scaling by one leaves the system unchanged. -/
  one_smul (Γ : System) : scale 1 Γ = Γ

  /-- A1, reflexivity: every state is accessible from itself, `X ≺ X`. -/
  A1 {Γ : System} (X : State Γ) : le X X
  /-- A2, transitivity: `X ≺ Y` and `Y ≺ Z` give `X ≺ Z`. -/
  A2 {Γ₁ Γ₂ Γ₃ : System} {X : State Γ₁} {Y : State Γ₂} {Z : State Γ₃} :
    le X Y → le Y Z → le X Z
  /-- A3, consistency: accessibility is preserved by composition —
  `X₁ ≺ Y₁` and `X₂ ≺ Y₂` give `(X₁, X₂) ≺ (Y₁, Y₂)`. -/
  A3 {Γ₁ Γ₂ Γ₃ Γ₄ : System}
      {X₁ : State Γ₁} {X₂ : State Γ₂} {Y₁ : State Γ₃} {Y₂ : State Γ₄} :
    le X₁ Y₁ → le X₂ Y₂ →
      le (state_of_comp_equiv.symm (X₁, X₂)) (state_of_comp_equiv.symm (Y₁, Y₂))
  /-- A4, scaling invariance: if `X ≺ Y` then `t • X ≺ t • Y` for every `t > 0`. -/
  A4 {Γ₁ Γ₂ : System} {X : State Γ₁} {Y : State Γ₂} {t : ℝ} (ht : 0 < t) :
    le X Y → le ((state_of_scale_equiv ht.ne.symm).symm X)
      ((state_of_scale_equiv ht.ne.symm).symm Y)
  /-- A5, splitting and recombination: for `0 < t < 1` a state is adiabatically equivalent
  to its split into a `t`-copy and a `(1−t)`-copy, `X ≈ (t • X, (1−t) • X)`. -/
  A5 {Γ : System} (X : State Γ) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    le X
      (state_of_comp_equiv.symm
        (((state_of_scale_equiv ht.1.ne').symm X),
          ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X))) ∧
    le (state_of_comp_equiv.symm
        (((state_of_scale_equiv ht.1.ne').symm X),
          ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X))) X
  /-- A6, stability: accessibility cannot be created by an infinitesimal perturbation.

  If `(X, epsilon_n Z₀)` is adiabatically accessible to `(Y, epsilon_n Z₁)` for some states
  `Z₀, Z₁` along a positive sequence `epsilon_n` tending to zero, then `X` is adiabatically
  accessible to `Y`. Lieb-Yngvason: one cannot enlarge the set of accessible states "with an
  infinitesimal grain of dust." -/
  A6_seq {ΓX ΓY ΓZ₀ ΓZ₁ : System} (X : State ΓX) (Y : State ΓY)
      (Z₀ : State ΓZ₀) (Z₁ : State ΓZ₁) :
    (∃ (ε_seq : ℕ → ℝ) (hpos : ∀ n, 0 < ε_seq n),
      Filter.Tendsto ε_seq Filter.atTop (nhds 0) ∧
      (∀ n,
        le
          (state_of_comp_equiv.symm
            (X, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₀))
          (state_of_comp_equiv.symm
            (Y, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₁)))) → le X Y

  /-- Coherence of casting along an equality of systems: transporting a state along the
  equality yields an adiabatically-equivalent state. This and the coherence fields below are
  not Lieb-Yngvason axioms — they are needed only because Lean does not identify
  propositionally-equal state spaces. -/
  state_equiv_coherence {Γ₁ Γ₂ : System} (h_sys : Γ₁ = Γ₂) (X : State Γ₁) :
    le X (Equiv.cast (congrArg State h_sys) X) ∧
    le (Equiv.cast (congrArg State h_sys) X) X
  /-- Coherence of composing with the zero system. -/
  comp_ZSystem_is_identity (Γ : System) (X : State Γ) :
    le (state_of_comp_equiv.symm (X, State_ZSystem_is_Unit.default)) X ∧
    le X (state_of_comp_equiv.symm (X, State_ZSystem_is_Unit.default))
  /-- Coherence of successive scaling: `t` applied to `s` applied to `X` agrees with `(t * s)`
  applied to `X`, up to adiabatic equivalence after the system cast. -/
  scale_coherence {t s : ℝ} (ht : t ≠ 0) (hs : s ≠ 0) {Γ : System} (X : State Γ) :
    let X_s := (state_of_scale_equiv hs).symm X
    let X_ts := (state_of_scale_equiv ht).symm X_s
    let X_mul := (state_of_scale_equiv (mul_ne_zero ht hs)).symm X
    let h_eq := smul_smul t s Γ
    le (Equiv.cast (congrArg State h_eq) X_mul) X_ts ∧
    le X_ts (Equiv.cast (congrArg State h_eq) X_mul)
  /-- Coherence of equal scaling factors. -/
  scale_eq_coherence {t₁ t₂ : ℝ} (h_eq : t₁ = t₂) (ht₁ : t₁ ≠ 0) {Γ : System}
      (X : State Γ) :
    let ht₂ : t₂ ≠ 0 := h_eq ▸ ht₁
    let X₁ := (state_of_scale_equiv ht₁).symm X
    let X₂ := (state_of_scale_equiv ht₂).symm X
    let h_sys_eq := congrArg (fun r => scale r Γ) h_eq
    le (Equiv.cast (congrArg State h_sys_eq) X₁) X₂ ∧
    le X₂ (Equiv.cast (congrArg State h_sys_eq) X₁)
  /-- Coherence of scaling by one. -/
  one_smul_coherence {Γ : System} (X : State Γ) :
    let X_1 := (state_of_scale_equiv (show (1 : ℝ) ≠ 0 from one_ne_zero)).symm X
    let h_eq := one_smul Γ
    le (Equiv.cast (congrArg State h_eq) X_1) X ∧
    le X (Equiv.cast (congrArg State h_eq) X_1)
  /-- Coherence of scaling a composed state. -/
  scale_comp_coherence {t : ℝ} (ht : t ≠ 0) {Γ₁ Γ₂ : System}
      (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let tXY := (state_of_scale_equiv ht).symm XY
    let tX := (state_of_scale_equiv ht).symm X
    let tY := (state_of_scale_equiv ht).symm Y
    let tXtY := state_of_comp_equiv.symm (tX, tY)
    let h_eq := scale_distrib_comp t Γ₁ Γ₂
    le (Equiv.cast (congrArg State h_eq) tXY) tXtY ∧
    le tXtY (Equiv.cast (congrArg State h_eq) tXY)
  /-- Coherence of commutativity of composition. -/
  comp_comm_coherence {Γ₁ Γ₂ : System} (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let YX := state_of_comp_equiv.symm (Y, X)
    let h_eq := comp_comm Γ₁ Γ₂
    le (Equiv.cast (congrArg State h_eq.symm) YX) XY ∧
    le XY (Equiv.cast (congrArg State h_eq.symm) YX)
  /-- Coherence of associativity of composition. -/
  comp_assoc_coherence {Γ₁ Γ₂ Γ₃ : System} (X : State Γ₁) (Y : State Γ₂)
      (Z : State Γ₃) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let XYZ_L := state_of_comp_equiv.symm (XY, Z)
    let YZ := state_of_comp_equiv.symm (Y, Z)
    let XYZ_R := state_of_comp_equiv.symm (X, YZ)
    let h_eq := comp_assoc Γ₁ Γ₂ Γ₃
    le (Equiv.cast (congrArg State h_eq) XYZ_L) XYZ_R ∧
    le XYZ_R (Equiv.cast (congrArg State h_eq) XYZ_L)

/-! ## C. Comparability

Two states are *comparable* when at least one is accessible from the other; they are
*adiabatically equivalent* when each is. Lieb-Yngvason's **comparison hypothesis** (CH)
asserts that any two states of one state space are comparable. Crucially CH is a
*hypothesis*, not one of A1-A6: the paper's programme is to *derive* it for simple systems
from the thermal axioms, so we keep it as a named `Prop` that later entropy
constructions carry as a separate assumption rather than folding it into accessibility.
`GlobalComparisonHypothesis` is the compound-system strengthening. -/

section Core

variable {System : Type u} [T : ThermoSystemCore System]

/-- The state of a composed system associated to a pair of component states. -/
def comp_state {Γ₁ Γ₂ : System} (p : T.State Γ₁ × T.State Γ₂) :
    T.State (T.comp Γ₁ Γ₂) :=
  T.state_of_comp_equiv.symm p

/-- The state of a nonzero-scaled system associated to a state of the original system. -/
def scale_state {t : ℝ} (ht : t ≠ 0) {Γ : System} (X : T.State Γ) :
    T.State (T.scale t Γ) :=
  (T.state_of_scale_equiv ht).symm X

/-- Two states are comparable if either is adiabatically accessible from the other,
`X ≺ Y ∨ Y ≺ X` (Lieb-Yngvason 1999, §II.A). -/
def Comparable {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) : Prop :=
  T.le X Y ∨ T.le Y X

/-- The comparison hypothesis for a single system: any two of its states are comparable.
Stated as a hypothesis, not an axiom — Lieb-Yngvason derive it for simple systems rather than
assuming it (§II.C, §III-IV). -/
def ComparisonHypothesis (Γ : System) : Prop :=
  ∀ X Y : T.State Γ, Comparable (T := T) X Y

/-- The global comparison hypothesis: any two states, possibly of different systems, are
comparable. This is named at A0 because later entropy constructions carry it as a separate
hypothesis rather than baking it into accessibility. -/
def GlobalComparisonHypothesis (System : Type u) [T : ThermoSystemCore System] : Prop :=
  ∀ {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂), Comparable (T := T) X Y

/-- Strict adiabatic accessibility `X ≺≺ Y`: `X ≺ Y` but not `Y ≺ X`. These are the
irreversible processes, the ones with strictly increasing entropy. -/
def StrictlyPrecedes {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) : Prop :=
  T.le X Y ∧ ¬ T.le Y X

namespace Comparable

/-- Comparability is symmetric. -/
lemma symm {Γ₁ Γ₂ : System} {X : T.State Γ₁} {Y : T.State Γ₂}
    (h : Comparable (T := T) X Y) : Comparable (T := T) Y X :=
  Or.symm h

end Comparable

/-! ## D. Core API

Small consequences that need only `ThermoSystemCore`. -/

/-- The zero-system state space is inhabited. -/
instance instInhabitedZState (System : Type u) [T : ThermoSystemCore System] :
    Inhabited (T.State T.ZSystem) :=
  ⟨T.State_ZSystem_is_Unit.default⟩

end Core

/-! ## E. World API

Notation (`≺`, `≈`, `⊗`, `•`, `≺≺`) and the preorder lemmas exposing axioms A1 and A2 as
reflexivity and transitivity, plus a `Trans` instance so accessibility chains compose in
`calc` blocks. -/

section World

variable {System : Type u} [TW : ThermoWorld System]

local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale
local infix:50 " ≺≺ " => StrictlyPrecedes (T := TW)

/-- Reflexivity of adiabatic accessibility, exposed as a lemma from A1. -/
lemma thermo_le_refl {Γ : System} (X : TW.State Γ) : X ≺ X :=
  TW.A1 X

/-- Transitivity of adiabatic accessibility, exposed as a lemma from A2. -/
lemma thermo_le_trans {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂}
    {Z : TW.State Γ₃} (hXY : X ≺ Y) (hYZ : Y ≺ Z) : X ≺ Z :=
  TW.A2 hXY hYZ

/-- Adiabatic equivalence is reflexive. -/
lemma thermo_equiv_refl {Γ : System} (X : TW.State Γ) : X ≈ X :=
  ⟨thermo_le_refl X, thermo_le_refl X⟩

/-- Adiabatic equivalence is symmetric. -/
lemma thermo_equiv_symm {Γ₁ Γ₂ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂}
    (h : X ≈ Y) : Y ≈ X :=
  And.symm h

/-- A `Trans` instance for calculations with adiabatic accessibility. -/
instance calcTransThermoLe {Γ₁ Γ₂ Γ₃ : System} :
    Trans (TW.le : TW.State Γ₁ → TW.State Γ₂ → Prop)
      (TW.le : TW.State Γ₂ → TW.State Γ₃ → Prop)
      (TW.le : TW.State Γ₁ → TW.State Γ₃ → Prop) where
  trans := TW.A2

end World

end Thermodynamics
