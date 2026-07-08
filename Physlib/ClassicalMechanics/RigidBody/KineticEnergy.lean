/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
public import Physlib.ClassicalMechanics.RigidBody.AngularVelocity
/-!

# Kinetic energy of a rigid body

For a rigid body rotating with angular velocity `ω` about its reference point the point at
position `r` has velocity `ω × r`, so its kinetic energy is `T = ½ ∫ |ω × r|² dm`. Since
`|ω × r|² = ω · (r × (ω × r))` and the angular momentum is `L = ∫ r × (ω × r) dm = I ω`, the
kinetic energy is the quadratic form `T = ½ ω · L = ½ ω · I ω` in the inertia tensor.

For a rigid body in motion the total kinetic energy is the mass integral of half the squared
speed of its points, `T = ½ ∫ v · v dm`. König's theorem splits it into the kinetic energy of
the centre of mass plus the rotational energy about the centre of mass,
`T = ½ M V · V + ½ ∫ |Ṙ (y − c)|² dm`: the cross term vanishes because the first moment of the
mass distribution about its centre of mass is zero. In three dimensions the rotational term is
`½ ∫ |ω × r|² dm`, with `ω` the angular velocity vector and `r` the position of the body point
relative to the centre of mass.

## References
- Landau and Lifshitz, Mechanics, Section 32.
-/

@[expose] public section

open Time Manifold Matrix RigidBody

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

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

namespace RigidBodyMotion

/-- The closed form `Ṙ(t) (y − c) + V(t)` of the velocity of the body point `y` at time `t`:
the rate of change of the orientation acting on the body-frame position, plus the centre-of-mass
velocity. It is polynomial in `y` for any motion, and for differentiable motions it agrees with
the honest point velocity `∂ₜ (displacement · y)`; see `velocityClosedForm_eq_velocity`. -/
noncomputable def velocityClosedForm {d : ℕ} (M : RigidBodyMotion d) (t : Time) (y : Space d) :
    Fin d → ℝ :=
  (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j)
    + (M.centerOfMassVelocity t : Fin d → ℝ)

/-- For a differentiable motion the closed-form velocity is the honest point velocity. -/
lemma velocityClosedForm_eq_velocity {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) (y : Space d) :
    M.velocityClosedForm t y = (M.velocity y t : Fin d → ℝ) := by
  funext i
  rw [velocityClosedForm, Pi.add_apply, ← M.velocity_eq_deriv_orientation y t i hR hX]

/-- The squared speed of a body point, in closed form, is a smooth function of the point. -/
lemma contDiff_velocityClosedForm_dotProduct {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    ContDiff ℝ ⊤ fun y : Space d => M.velocityClosedForm t y ⬝ᵥ M.velocityClosedForm t y := by
  simp only [velocityClosedForm, dotProduct, Matrix.mulVec, Pi.add_apply]
  fun_prop

/-- The total kinetic energy of a rigid body in motion at time `t`: half the mass integral of the
squared speed of the body points, `T = ½ ∫ v · v dm`, with the velocity of the point `y` written
in the closed form `Ṙ(t) (y − c) + V(t)`, which is polynomial in `y` for any motion. For
differentiable motions this is the honest point velocity `∂ₜ (displacement · y)`; see
`kineticEnergy_eq_integral_velocity`. -/
noncomputable def kineticEnergy {d : ℕ} (M : RigidBodyMotion d) (t : Time) : ℝ :=
  (1 / 2) * M.ρ (cmap (fun y => M.velocityClosedForm t y ⬝ᵥ M.velocityClosedForm t y)
    (M.contDiff_velocityClosedForm_dotProduct t))

/-- For a differentiable motion the total kinetic energy is the mass integral of half the squared
speed of the body points, `T = ½ ∫ v · v dm` with `v` the honest point velocity
`∂ₜ (displacement · y)`: the closed-form integrand of `kineticEnergy` agrees with the velocity. -/
lemma kineticEnergy_eq_integral_velocity {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) :
    M.kineticEnergy t = (1 / 2) * M.ρ (cmap
      (fun y => (M.velocity y t : Fin d → ℝ) ⬝ᵥ (M.velocity y t : Fin d → ℝ))
      (by
        simp only [← M.velocityClosedForm_eq_velocity t hR hX]
        exact M.contDiff_velocityClosedForm_dotProduct t)) := by
  rw [kineticEnergy]
  congr 2
  ext y
  simp only [cmap_apply, M.velocityClosedForm_eq_velocity t hR hX]

/-- **König's theorem**, general form: the total kinetic energy of a rigid body in motion splits
into the kinetic energy of the centre of mass plus the rotational energy about the centre of
mass, `T = ½ M V · V + ½ ∫ |Ṙ (y − c)|² dm`. The cross term vanishes because the first moment of
the mass distribution about its centre of mass is zero. -/
theorem kineticEnergy_eq_translational_add_rotational {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (h : M.mass ≠ 0) :
    M.kineticEnergy t
      = (1 / 2) * M.mass * ((M.centerOfMassVelocity t : Fin d → ℝ) ⬝ᵥ
          (M.centerOfMassVelocity t : Fin d → ℝ))
        + (1 / 2) * M.ρ (cmap (fun y =>
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) ⬝ᵥ
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j))
          (by simp only [dotProduct, Matrix.mulVec]; fun_prop)) := by
  have hsplit : cmap (fun y => M.velocityClosedForm t y ⬝ᵥ M.velocityClosedForm t y)
        (M.contDiff_velocityClosedForm_dotProduct t)
      = cmap (fun y =>
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) ⬝ᵥ
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j))
          (by simp only [dotProduct, Matrix.mulVec]; fun_prop)
        + ∑ j, (2 * (((M.centerOfMassVelocity t : Fin d → ℝ) ᵥ*
              ∂ₜ (fun s => (M.orientation s).1) t) j)) •
            cmap (fun y => y j - M.centerOfMass j) (by fun_prop)
        + ((M.centerOfMassVelocity t : Fin d → ℝ) ⬝ᵥ (M.centerOfMassVelocity t : Fin d → ℝ)) •
            (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) := by
    ext y
    simp only [cmap_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_smul, ContMDiffMap.coe_one,
      Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, velocityClosedForm]
    rw [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
      cmap_apply, smul_eq_mul]
    rw [add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j)
        (M.centerOfMassVelocity t : Fin d → ℝ),
      dotProduct_mulVec (M.centerOfMassVelocity t : Fin d → ℝ)
        (∂ₜ (fun s => (M.orientation s).1) t) (fun j => y j - M.centerOfMass j)]
    simp only [dotProduct, two_mul, add_mul, Finset.sum_add_distrib]
    ring
  rw [kineticEnergy, hsplit, map_add, map_add, map_sum]
  simp only [map_smul, M.rho_coord_sub_centerOfMass h, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, M.rho_one]
  ring

/-- **König's theorem** in three dimensions: the total kinetic energy of a rigid body in motion
splits as `T = ½ M V · V + ½ ∫ |ω × r|² dm`, the kinetic energy of the centre of mass plus the
rotational energy of the spinning about it, where `ω` is the angular velocity vector and
`r = displacement − comTrajectory` is the position of the body point relative to the centre of
mass. -/
theorem kineticEnergy_eq_translational_add_angularVelocity (M : RigidBodyMotion 3) (t : Time)
    (h : M.mass ≠ 0) (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    M.kineticEnergy t
      = (1 / 2) * M.mass * ((M.centerOfMassVelocity t : Fin 3 → ℝ) ⬝ᵥ
          (M.centerOfMassVelocity t : Fin 3 → ℝ))
        + (1 / 2) * M.ρ (cmap (fun y =>
            (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j) ⬝ᵥ
            (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j))
          (by
            exact (contDiff_cross_dotProduct_cross (M.angularVelocity t)).comp
              (contDiff_pi.mpr fun j =>
                ((Space.eval_contDiff j).comp (M.displacement_contDiff t)).sub
                  contDiff_const))) := by
  rw [M.kineticEnergy_eq_translational_add_rotational t h]
  congr 1
  congr 2
  ext y
  simp only [cmap_apply, M.deriv_orientation_mulVec_eq_angularVelocity_cross y t hR]

end RigidBodyMotion
