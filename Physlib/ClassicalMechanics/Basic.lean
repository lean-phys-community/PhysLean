/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# A. Classical mechanics

Classical mechanics describes the motion of physical systems using trajectories, forces,
energies, and variational principles. Physlib develops both general formulations of the subject
and formally verified examples of mechanical systems.

## A.1. Scope

The general infrastructure includes the Euler–Lagrange equations, Hamilton's equations, and
relations between equivalent Lagrangian descriptions. Concrete models cover free particles,
harmonic and damped oscillators, pendula, rigid bodies, orbital mechanics, scattering, vibrations,
and wave equations.

## A.2. Current status

This module is an overview and currently introduces no declarations. The definitions and results
for each topic live in the corresponding submodules under `Physlib.ClassicalMechanics`.

## A.3. Future work

Shared declarations should be added here only when they apply across several areas of classical
mechanics. Definitions and results specific to one physical system should remain in its dedicated
module so that the library stays navigable.

-/

@[expose] public section
