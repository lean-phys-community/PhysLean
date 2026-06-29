/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.LinearAlgebra.UnitaryGroup
/-!

# Rigid body motion

The static `RigidBody` records a body-fixed mass distribution. To describe a rigid body *in
motion* we record, in addition, the trajectory of its centre of mass in the inertial frame and the
body's time-dependent orientation (a rotation about the centre of mass).

From this configuration we define the velocity of the centre of mass and the body's linear
momentum. The reference point is taken to be the centre of mass, following the decomposition of
a rigid motion into a translation of the centre of mass plus a rotation about it.

## References
- Landau and Lifshitz, Mechanics, Section 32.
-/

@[expose] public section

open Time Manifold

/-- A motion of a rigid body in `d`-dimensional space: the body together with the inertial-frame
trajectory of its centre of mass and its time-dependent orientation (a rotation about the centre
of mass). -/
structure RigidBodyMotion (d : ℕ) extends RigidBody d where
  /-- The position of the centre of mass in the inertial frame as a function of time. -/
  comTrajectory : Time → Space d
  /-- The orientation of the body, a rotation about the centre of mass, as a function of time. -/
  orientation : Time → Matrix.specialOrthogonalGroup (Fin d) ℝ

namespace RigidBodyMotion

/-- The velocity of the centre of mass of a rigid body in motion, defined as the time-derivative
of its centre-of-mass trajectory. This is the velocity `V` in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body. -/
noncomputable def centerOfMassVelocity {d : ℕ} (M : RigidBodyMotion d) : Time → Space d :=
  ∂ₜ M.comTrajectory

lemma centerOfMassVelocity_eq {d : ℕ} (M : RigidBodyMotion d) :
    M.centerOfMassVelocity = ∂ₜ M.comTrajectory := rfl

/-- A rigid body whose centre of mass is stationary has zero centre-of-mass velocity. -/
lemma centerOfMassVelocity_of_comTrajectory_const {d : ℕ} (M : RigidBodyMotion d) (c : Space d)
    (h : M.comTrajectory = fun _ => c) : M.centerOfMassVelocity = 0 := by
  rw [centerOfMassVelocity_eq, h]
  funext t
  exact Time.deriv_const c

/-- The linear momentum of a rigid body in motion: the total mass times the velocity of the
centre of mass. -/
noncomputable def linearMomentum {d : ℕ} (M : RigidBodyMotion d) : Time → Space d :=
  fun t => M.mass • M.centerOfMassVelocity t

lemma linearMomentum_eq {d : ℕ} (M : RigidBodyMotion d) :
    M.linearMomentum = fun t => M.mass • M.centerOfMassVelocity t := rfl

/-- The rigid displacement carrying the body frame into the inertial frame at time `t`: the
rotation `orientation t` about the centre of mass, followed by the translation placing the centre
of mass at `comTrajectory t`. -/
noncomputable def displacement {d : ℕ} (M : RigidBodyMotion d) (t : Time) : Space d → Space d :=
  fun y => ⟨fun k => ∑ j, (M.orientation t).val k j * (y j - M.centerOfMass j) +
    M.comTrajectory t k⟩

lemma displacement_contDiff {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    ContDiff ℝ ⊤ (M.displacement t) := by
  unfold displacement
  fun_prop

/-- The mass distribution of the rigid body in motion at time `t`: the pushforward of the
body-fixed mass distribution along the rigid displacement, acting on a test function `f` by
`f ↦ ρ (f ∘ displacement t)`. -/
noncomputable def massDistribution {d : ℕ} (M : RigidBodyMotion d) (t : Time) : RigidBody d where
  ρ :=
    { toFun := fun f => M.ρ (f.comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩)
      map_add' := by
        intro f g
        have h : (f + g).comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩ =
            f.comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩ +
            g.comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩ := by
          ext y; simp
        rw [h, map_add]
      map_smul' := by
        intro r f
        have h : (r • f).comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩ =
            r • f.comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩ := by
          ext y; simp
        rw [h]
        exact map_smul M.ρ r _ }

/-- The motion preserves the total mass: the mass distribution at any time `t` has the same total
mass as the body. -/
@[simp]
lemma massDistribution_mass {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    (M.massDistribution t).mass = M.mass := by
  simp only [RigidBody.mass, massDistribution, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1

end RigidBodyMotion
