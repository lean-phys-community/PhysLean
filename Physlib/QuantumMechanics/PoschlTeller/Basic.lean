/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.Mathematics.Trigonometry.Tanh
public import Physlib.Meta.TODO.Basic
/-!

# 1d Pöschl-Teller

## i. Overview

The Pöschl-Teller potential, `$V(x) \propto -\mathrm{sech}^2{(\kappa x)}$`, gives rise
to a one-dimensional quantum system for which the energy eigenvalues, energy eigenstates and
scattering data can be computed exactly. Notably, the potential is _reflectionless_ when
the parameter controlling its depth is a positive integer.

## ii. Key results

## iii. Table of contents

- A. Potential function
- B. Hilbert space
- C. Operators
  - C.1. Kinetic energy
  - C.2. Potential energy
  - C.3. Hamiltonian
  - C.4. Creation and annihilation operators
    - C.4.1. On Schwartz functions
    - C.4.2. As unbounded operators
- D. As a quantum system

## iv. References

- https://arxiv.org/pdf/2411.14941

-/
@[expose] public section

TODO "Define the Hamiltonian and related operators for the Pöschl-Teller quantum system."

TODO "Develop the eigensystem of the Hamiltonian for the Pöschl-Teller quantum system
  using properties of the creation/annihilation operators
  (e.g. following https://arxiv.org/pdf/2411.14941)."

TODO "Prove that the Pöschl-Teller potential is reflectionless."

noncomputable section

namespace QuantumMechanics

open Complex Constants Real SchwartzMap

/-- A Pöschl-Teller system is specified by the particle mass `m`, the width parameter `κ`,
  and family number `N` (all positive). --/
structure PoschlTeller where
  /-- mass of the particle -/
  m : ℝ
  /-- width parameter of the potential -/
  κ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- width parameter of the potential is positive
  N_pos : 0 < N -- family number is positive

namespace PoschlTeller

variable (Q : PoschlTeller)

/-!
## A. Potential function
-/

/-- The Pöschl-Teller potential is `-(ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2)`. --/
def potential (x : Space 1) : ℝ :=
  -(ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / (2 * Q.m * Real.cosh (Q.κ * x 0) ^ 2)

/-!
## B. Hilbert space
-/

/-- The Hilbert space for the Pöschl-Teller system is `SpaceDHilbertSpace 1`. -/
@[nolint unusedArguments]
abbrev HS (_ : PoschlTeller) : Type _ := SpaceDHilbertSpace 1

/-!
## C. Operators
-/

/-!
### C.1. Kinetic energy
-/

/-!
### C.2. Potential energy
-/

/-!
### C.3. Hamiltonian
-/

/-!
### C.4. Creation and annihilation operators
-/

/-!
#### C.4.1. On Schwartz functions
-/

/-- Pointwise multiplication of Schwartz maps by `tanh(κx)`. -/
def tanhCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  smulLeftCLM ℂ (ofReal ∘ fun x => tanh (Q.κ * x 0))

/-- The creation operator, `1/√(2m) (P + iℏκ tanh(κX))` -/
def creationCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  (1 / sqrt (2 * Q.m)) • momentumCLM 0 + (I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhCLM

/-- The annihilation operator, `1/√(2m) (P - iℏκ tanh(κX))` -/
def annihilationCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  (1 / sqrt (2 * Q.m)) • momentumCLM 0 + (-I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhCLM

/-!
#### C.4.2. As unbounded operators
-/

/-- The unbounded operator defined by pointwise multiplication by `tanh(κx)`. -/
def tanhOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 _ (ofReal ∘ fun x => Real.tanh (Q.κ * x 0))

/-- The creation unbounded operator, `1/√(2m) (P + iℏκ tanh(κX))` -/
def creationOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  (1 / sqrt (2 * Q.m)) • momentumOperator 0 + (I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhOperator

/-- The annihilation unbounded operator, `1/√(2m) (P - iℏκ tanh(κX))` -/
def annihilationOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  (1 / sqrt (2 * Q.m)) • momentumOperator 0 + (-I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhOperator

/-!
## D. As a quantum system
-/

end PoschlTeller
end QuantumMechanics
end
