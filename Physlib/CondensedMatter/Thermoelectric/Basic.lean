/-
Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Barbalinardo
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
/-!

# Thermoelectric figure of merit

## i. Overview

A thermoelectric material converts a temperature difference into electrical power.
Its performance at absolute temperature `T` is captured by the dimensionless
figure of merit

  zT = σ S² T / (κₗ + κₑ),

where `S` is the Seebeck coefficient, `σ` the electrical conductivity, and
`κₗ`, `κₑ` the lattice (phonon) and electronic contributions to the thermal
conductivity. The numerator groups into the power factor `PF = σ S²`.

In this file all quantities are real numbers in a fixed consistent system of
units, following the convention of `Physlib.Thermodynamics.IdealGas.Basic`.

## ii. Key results

- `powerFactor`: the thermoelectric power factor `σ S²`.
- `totalThermalConductivity`: the total thermal conductivity `κₗ + κₑ`.
- `figureOfMerit`: the dimensionless figure of merit `zT`.
- `figureOfMerit_eq`: the flat form `zT = σ S² T / (κₗ + κₑ)`.
- `figureOfMerit_pos`: positivity of `zT` for a conducting material with a
  nonzero Seebeck coefficient at positive temperature.
- `figureOfMerit_le_of_le`: lowering the lattice thermal conductivity raises
  `zT`, the phonon-glass electron-crystal design principle.

## iii. Table of contents

- A. The power factor
- B. The total thermal conductivity
- C. The figure of merit
  - C.1. Equalities for the figure of merit
  - C.2. Positivity of the figure of merit
  - C.3. Monotonicity in the lattice thermal conductivity

## iv. References

- Ioffe, A.F., *Semiconductor Thermoelements and Thermoelectric Cooling*,
  Infosearch (1957).
- Snyder, G.J., Toberer, E.S., *Complex thermoelectric materials*,
  Nature Materials 7, 105–114 (2008).

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace Thermoelectric

/-!

## A. The power factor

-/

/-- The thermoelectric power factor `PF = σ S²` of a material with Seebeck
coefficient `S` and electrical conductivity `σ`. -/
def powerFactor (S σ : ℝ) : ℝ := σ * S ^ 2

/-- The power factor is positive for a conducting material (`0 < σ`) with a
nonzero Seebeck coefficient. -/
lemma powerFactor_pos {S σ : ℝ} (hσ : 0 < σ) (hS : S ≠ 0) :
    0 < powerFactor S σ := by
  unfold powerFactor
  positivity

/-!

## B. The total thermal conductivity

-/

/-- The total thermal conductivity `κₗ + κₑ`, the sum of the lattice (phonon)
contribution `κₗ` and the electronic contribution `κₑ`. -/
def totalThermalConductivity (κl κe : ℝ) : ℝ := κl + κe

/-- The total thermal conductivity is positive when the lattice contribution is
positive and the electronic contribution is nonnegative. -/
lemma totalThermalConductivity_pos {κl κe : ℝ} (hl : 0 < κl) (he : 0 ≤ κe) :
    0 < totalThermalConductivity κl κe := by
  unfold totalThermalConductivity
  positivity

/-!

## C. The figure of merit

-/

/-- The dimensionless thermoelectric figure of merit
`zT = PF · T / (κₗ + κₑ)` of a material with Seebeck coefficient `S`,
electrical conductivity `σ`, lattice thermal conductivity `κl`, electronic
thermal conductivity `κe`, at absolute temperature `T`. -/
def figureOfMerit (S σ κl κe T : ℝ) : ℝ :=
  powerFactor S σ * T / totalThermalConductivity κl κe

/-!

### C.1. Equalities for the figure of merit

-/

/-- The figure of merit in its standard flat form `zT = σ S² T / (κₗ + κₑ)`. -/
lemma figureOfMerit_eq (S σ κl κe T : ℝ) :
    figureOfMerit S σ κl κe T = σ * S ^ 2 * T / (κl + κe) := by
  unfold figureOfMerit powerFactor totalThermalConductivity
  ring

/-!

### C.2. Positivity of the figure of merit

-/

/-- The figure of merit is positive for a conducting material (`0 < σ`) with a
nonzero Seebeck coefficient at positive temperature, when the lattice thermal
conductivity is positive and the electronic one nonnegative. -/
lemma figureOfMerit_pos {S σ κl κe T : ℝ}
    (hσ : 0 < σ) (hS : S ≠ 0)
    (hl : 0 < κl) (he : 0 ≤ κe) (hT : 0 < T) :
    0 < figureOfMerit S σ κl κe T :=
  div_pos (mul_pos (powerFactor_pos hσ hS) hT)
    (totalThermalConductivity_pos hl he)

/-!

### C.3. Monotonicity in the lattice thermal conductivity

-/

/-- Lowering the lattice thermal conductivity raises the figure of merit: if
`κl ≤ κl'` then `zT(κl') ≤ zT(κl)`, all other properties held fixed. This is
the phonon-glass electron-crystal design principle: scatter phonons without
degrading electronic transport. -/
lemma figureOfMerit_le_of_le {S σ κl κl' κe T : ℝ}
    (hσ : 0 < σ) (hS : S ≠ 0)
    (hl : 0 < κl) (he : 0 ≤ κe) (hT : 0 < T)
    (h : κl ≤ κl') :
    figureOfMerit S σ κl' κe T ≤ figureOfMerit S σ κl κe T := by
  unfold figureOfMerit totalThermalConductivity
  have hnum : 0 ≤ powerFactor S σ * T :=
    le_of_lt (mul_pos (powerFactor_pos hσ hS) hT)
  have hden : 0 < κl + κe := add_pos_of_pos_of_nonneg hl he
  gcongr

end Thermoelectric

end CondensedMatter
