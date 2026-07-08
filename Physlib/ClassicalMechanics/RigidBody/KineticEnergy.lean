/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
/-!

# Rotational kinetic energy of a rigid body

For a rigid body rotating with angular velocity `ω` about its reference point the point at
position `r` has velocity `ω × r`, so its kinetic energy is `T = ½ ∫ |ω × r|² dm`. Since
`|ω × r|² = ω · (r × (ω × r))` and the angular momentum is `L = ∫ r × (ω × r) dm = I ω`, the
kinetic energy is the quadratic form `T = ½ ω · L = ½ ω · I ω` in the inertia tensor.

## References
- Landau and Lifshitz, Mechanics, Section 32.
-/

@[expose] public section

open Manifold Matrix

namespace RigidBody

/-- The rotational kinetic energy of a rigid body rotating with angular velocity `ω` about its
reference point: half the contraction of `ω` with the inertia tensor, `T = ½ ω · (I ω)`. -/
noncomputable def rotationalKineticEnergy (R : RigidBody 3) (ω : Fin 3 → ℝ) : ℝ :=
  (1 / 2) * (ω ⬝ᵥ R.inertiaTensor *ᵥ ω)

/-- The rotational kinetic energy is half the contraction of the angular velocity with the angular
momentum: `T = ½ ω · L`. -/
lemma rotationalKineticEnergy_eq_angularMomentum (R : RigidBody 3) (ω : Fin 3 → ℝ) :
    R.rotationalKineticEnergy ω = (1 / 2) * (ω ⬝ᵥ R.angularMomentum ω) := by
  rw [rotationalKineticEnergy, angularMomentum_eq_inertiaTensor_mulVec]

/-- The rotational kinetic energy equals the mass integral of the local rotational speed squared:
`T = ½ ∫ |ω × r|² dm`. -/
theorem rotationalKineticEnergy_eq_integral (R : RigidBody 3) (ω : Fin 3 → ℝ) :
    R.rotationalKineticEnergy ω
      = (1 / 2) * R.ρ ⟨fun x => (ω ⨯₃ (x : Fin 3 → ℝ)) ⬝ᵥ (ω ⨯₃ (x : Fin 3 → ℝ)),
        ContDiff.contMDiff <| (contDiff_cross_dotProduct_cross ω).comp
          (contDiff_pi.mpr fun i => Space.eval_contDiff i)⟩ := by
  rw [rotationalKineticEnergy_eq_angularMomentum]
  congr 1
  simp_rw [dotProduct, angularMomentum, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  ext x
  rw [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    ContMDiffMap.coeFn_mk, smul_eq_mul]
  exact dotProduct_cross_cross_self (x : Fin 3 → ℝ) ω

end RigidBody
