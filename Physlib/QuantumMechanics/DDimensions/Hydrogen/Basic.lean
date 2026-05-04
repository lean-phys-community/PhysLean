/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Momentum
public import Physlib.QuantumMechanics.DDimensions.Operators.Position
/-!

# Hydrogen atom

This module introduces the `d`-dimensional hydrogen atom with `1/r` potential.

In addition to the dimension `d`, the quantum mechanical system is characterized by
a mass `m > 0` and constant `k` appearing in the potential `V = -k/r`.
The standard hydrogen atom has `d=3`, `m = mₑmₚ/(mₑ + mₚ) ≈ mₑ` and `k = e²/4πε₀`.

The potential `V = -k/r` is singular at the origin. To address this we define a regularized
Hamiltonian in which the potential is replaced by `-k·r(ε)⁻¹`, where `r(ε)² = ‖x‖² + ε²`.
This goes by several names including "soft-core" and "truncated" Coulomb potential.
e.g. see https://doi.org/10.1103/PhysRevA.80.032507 and https://doi.org/10.1063/1.3290740.

-/

@[expose] public section

namespace QuantumMechanics
open SchwartzMap

/-- A hydrogen atom is characterized by the number of spatial dimensions `d`,
  the mass `m` and the coefficient `k` for the `1/r` potential. -/
structure HydrogenAtom where
  /-- Number of spatial dimensions -/
  d : ℕ

  /-- Mass (positive) -/
  m : ℝ
  hm : 0 < m

  /-- Coefficient in potential (positive for attractive) -/
  k : ℝ

namespace HydrogenAtom
noncomputable section

variable (H : HydrogenAtom)

@[simp]
lemma m_ne_zero : H.m ≠ 0 := by linarith [H.hm]

set_option backward.isDefEq.respectTransparency false in
/-- The hydrogen atom Hamiltonian regularized by `ε ≠ 0` is defined to be
  `𝐇(ε) ≔ (2m)⁻¹𝐩² - k·𝐫(ε)⁻¹`. -/
def hamiltonianReg (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 * H.m)⁻¹ • (𝐩 ⬝ᵥ 𝐩) - H.k • 𝐫₀ ε (-1)

end
end HydrogenAtom
end QuantumMechanics
