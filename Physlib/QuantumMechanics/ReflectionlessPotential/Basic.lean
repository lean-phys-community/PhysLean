/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.Mathematics.Trigonometry.Tanh
public import Physlib.Meta.TODO.Basic
/-!

# 1d Reflectionless Potential

The quantum reflectionless potential in 1d.
This file contains
- the definition of the reflectionless potential as defined https://arxiv.org/pdf/2411.14941
- properties of reflectionless potentials

## TODO
- Define creation and annihilation operators for reflectionless potentials
- Write the proof of the general solution of the reflectionless potential using the creation and
annihilation operators
- Show reflectionless properties
-/

TODO "Refactor to use `SpaceDHilbertSpace 1`."

TODO "Refactor to use `QuantumMechanics.PlanckConstant`."

@[expose] public section

namespace QuantumMechanics
open Real
open Complex Constants SchwartzMap
open HilbertSpace
open NNReal
open Field

namespace OneDimension

/-- A reflectionless potential is specified by three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, the
  parameter `κ`, as well as a positive integer family number `N`.
  All of these parameters are assumed to be positive. --/
structure ReflectionlessPotential where
  /-- mass of the particle -/
  m : ℝ
  /-- parameter of the reflectionless potential -/
  κ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- parameter of the reflectionless potential is positive
  N_pos : 0 < N -- family number is positive

namespace ReflectionlessPotential

variable (Q : ReflectionlessPotential)

/-!
## Theorems
TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
-/

/-- Define the reflectionless potential as
  V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) --/
noncomputable def potential (x : Space 1) : ℝ :=
  - (ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / (2 * Q.m * Real.cosh (Q.κ * x 0) ^ 2)

/-- Define tanh(κ X) multiplication pointwise as a Schwartz map -/
noncomputable def tanhCLM (Q : ReflectionlessPotential) : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  smulLeftCLM ℂ (ofReal ∘ fun x => tanh (Q.κ * x 0))

/-- Creation operator: a† as defined in https://arxiv.org/pdf/2411.14941
  a† = 1/√(2m) (P + iℏκ tanh(κX)) -/
noncomputable def creationCLM (Q : ReflectionlessPotential) : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  (1 / Real.sqrt (2 * Q.m)) • momentumCLM 0 + ((I * ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhCLM

/-- Annihilation operator: a as defined in https://arxiv.org/pdf/2411.14941
  a = 1/√(2m) (P - iℏκ tanh(κX)) -/
noncomputable def annihilationCLM (Q : ReflectionlessPotential) :
  𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
    (1 / Real.sqrt (2 * Q.m)) • momentumCLM 0 + ((-I * ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhCLM

end ReflectionlessPotential
end OneDimension
end QuantumMechanics
