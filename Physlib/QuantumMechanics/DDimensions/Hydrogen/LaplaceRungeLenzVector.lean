/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Hydrogen.Basic
public import Physlib.QuantumMechanics.DDimensions.Operators.Commutation
/-!

# Laplace-Runge-Lenz vector

In this file we define
- The (regularized) LRL vector operator for the quantum mechanical hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`.
- The square of the LRL vector operator, `𝐀(ε)² ≔ 𝐀(ε)ᵢ𝐀(ε)ᵢ`.

The main results are
- The commutators `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` in `angularMomentum_commutation_lrl`
- The commutators `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = -iℏ 2m 𝐇(ε)𝐋ᵢⱼ` in `lrl_commutation_lrl`
- The commutators `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏε²(⋯)` in `hamiltonianReg_commutation_lrl`
- The relation `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² + ε²(⋯)` in `lrlOperatorSqr_eq`

-/

@[expose] public section

namespace QuantumMechanics
namespace HydrogenAtom
noncomputable section
open Complex Constants
open KroneckerDelta
open ContinuousLinearMap SchwartzMap

variable (H : HydrogenAtom)

/-- The (regularized) Laplace-Runge-Lenz vector operator for the `d`-dimensional hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`. -/
def lrlOperator (ε : ℝˣ) (i : Fin H.d) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 : ℝ)⁻¹ • ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j]) - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i]

/-- The square of the LRL vector operator, `𝐀(ε)² ≔ 𝐀(ε)ᵢ𝐀(ε)ᵢ`. -/
def lrlOperatorSqr (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  ∑ i, (H.lrlOperator ε i) ∘L (H.lrlOperator ε i)

/-- `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i = 𝐱[i] ∘L 𝐩² - (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i]
    + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  rw [lrlOperator, sub_left_inj] -- mk·r⁻¹x terms match exactly
  calc
    _ = (2 : ℂ)⁻¹ • ∑ j, ((𝐩[j] ∘L 𝐱[i]) ∘L 𝐩[j] + 𝐱[i] ∘L 𝐩[j] ∘L 𝐩[j]
        - ((𝐩[j] ∘L 𝐱[j]) ∘L 𝐩[i] + 𝐱[j] ∘L 𝐩[j] ∘L 𝐩[i])) := by
      simp [angularMomentumOperator, add_sub, comp_assoc, sub_add_eq_add_sub, sub_sub,
        momentum_comp_commute, ← Complex.coe_smul]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱[i] ∘L 𝐩[j] ∘L 𝐩[j] - (I * ℏ) • δ[i,j] • 𝐩[j]
        - ((2 : ℂ) • (𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i] - (I * ℏ) • 𝐩[i])) := by
      simp only [momentum_comp_position_eq, sub_comp, smul_comp, id_comp, sub_add_eq_add_sub,
        comp_assoc, two_smul, eq_one_of_same, one_smul]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱[i] ∘L 𝐩[j] ∘L 𝐩[j] - (2 : ℂ) • (𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i]
        + (I * ℏ) • 𝐩[i] - (I * ℏ) • δ[i,j] • 𝐩[j]) := by
      simp_rw [sub_sub_sub_comm, sub_sub_eq_add_sub]
    _ = 𝐱[i] ∘L ∑ j, 𝐩[j] ∘L 𝐩[j] - (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i] + ((2⁻¹ * I * ℏ) • H.d • 𝐩[i]
        - (2⁻¹ * I * ℏ) • 𝐩[i]) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, sum_smul,
        smul_add, smul_sub, smul_smul, comp_finset_sum, finset_sum_comp, mul_assoc, add_sub_assoc]
      norm_num
  rw [momentumOperatorSqr, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← sub_smul]
  ring_nf

/-- `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐋[i,j] ∘L 𝐩[j]
    + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  rw [lrlOperator_eq, sub_left_inj, add_left_inj]
  symm
  trans ∑ j, 𝐱[i] ∘L 𝐩[j] ∘L 𝐩[j] - ∑ j, (𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i]
  · simp [angularMomentumOperator, comp_assoc, momentum_comp_commute]
  simp [← comp_finset_sum, ← finset_sum_comp, momentumOperatorSqr]

/-- `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq'' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐩[j] ∘L 𝐋[i,j]
    - (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  trans (2 : ℝ) • H.lrlOperator ε i - H.lrlOperator ε i
  · simp [two_smul]
  nth_rw 2 [lrlOperator_eq']
  simp only [lrlOperator, Finset.sum_add_distrib, smul_add, smul_sub, smul_smul]
  ring_nf
  ext
  simp only [one_smul, coe_sub', coe_smul', Pi.sub_apply, ContinuousLinearMap.add_apply,
    Pi.smul_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, real_smul,
    ofReal_mul, ofReal_ofNat]
  ring

/-- The operator `𝐱ᵢ𝐩ᵢ` on Schwartz maps. -/
private def positionDotMomentum (d : ℕ) := ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i]

/-- The operator `𝐱ᵢ𝐩²` on Schwartz maps. -/
private def positionCompMomentumSqr {d : ℕ} (i : Fin d) := 𝐱[i] ∘L 𝐩²

/-- The operator `(𝐱ⱼ𝐩ⱼ)𝐱ᵢ` on Schwartz maps. -/
private def positionDotMomentumCompMomentum {d : ℕ} (i : Fin d) := positionDotMomentum d ∘L 𝐩[i]

/-- The operator `½iℏ(d-1)𝐩ᵢ` on Schwartz maps. -/
private def constMomentum {d : ℕ} (i : Fin d) := (2⁻¹ * I * ℏ * (d - 1)) • 𝐩[i]

/-- The operator `mk·𝐫(ε)⁻¹𝐱ᵢ` on Schwartz maps. -/
private def constRadiusRegInvCompPosition (ε : ℝˣ) (i : Fin H.d) := (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i]

/-
## Angular momentum / LRL vector commutators
-/

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` -/
@[sorryful]
lemma angularMomentum_commutation_lrl (ε : ℝˣ) (i j k : Fin H.d) :
    ⁅𝐋[i,j], H.lrlOperator ε k⁆ = (Complex.I * ℏ * δ[i,k]) • H.lrlOperator ε j
    - (Complex.I * ℏ * δ[j,k]) • H.lrlOperator ε i := by
  sorry

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)²⁆ = 0` -/
@[sorryful]
lemma angularMomentum_commutation_lrlSqr (ε : ℝˣ) (i j : Fin H.d) :
    ⁅𝐋[i,j], H.lrlOperatorSqr ε⁆ = 0 := by
  unfold lrlOperatorSqr
  simp only [lie_sum, lie_leibniz, H.angularMomentum_commutation_lrl]
  simp only [comp_sub, comp_smul, sub_comp, smul_comp]
  dsimp only [kroneckerDelta]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `⁅𝐋², 𝐀(ε)²⁆ = 0` -/
@[sorryful]
lemma angularMomentumSqr_commutation_lrlSqr (ε : ℝˣ) :
    ⁅angularMomentumOperatorSqr (d := H.d), H.lrlOperatorSqr ε⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  simp [sum_lie, leibniz_lie, H.angularMomentum_commutation_lrlSqr]

/-

## LRL / LRL commutators

To compute the commutator `⁅𝐀ᵢ(ε), 𝐀ⱼ(ε)⁆` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ ≕ f1ᵢ - f2ᵢ + f3ᵢ - f4ᵢ`
- Organize the sixteen terms which result from expanding `⁅f1ᵢ-f2ᵢ+f3ᵢ-f4ᵢ, f1ⱼ-f2ⱼ+f3ⱼ-f4ⱼ⁆`
  into four diagonal terms such as `⁅f1ᵢ, f1ⱼ⁆` and six off-diagonal pairs such as
  `⁅f1ᵢ, f3ⱼ⁆ + ⁅f3ᵢ, f1ⱼ⁆ = ⁅f1ᵢ, f3ⱼ⁆ - ⁅f1ⱼ, f3ᵢ⁆`.
- Compute the diagonal commutators and off-diagonal pairs individually. Many vanish, and those
  that don't are all of the form `iℏ (⋯) 𝐋ᵢⱼ` (as they must to be antisymmetric in `i,j`).
- Collect terms.

-/

private lemma positionDotMomentum_commutation_position {d : ℕ} (i : Fin d) :
    ⁅positionDotMomentum d, 𝐱[i]⁆ = (-I * ℏ) • 𝐱[i] := by
  trans ∑ j, 𝐱[j] ∘L ⁅𝐩[j], 𝐱[i]⁆
  · simp [positionDotMomentum, sum_lie, leibniz_lie]
  simp_rw [← lie_skew 𝐩[_] 𝐱[_], position_commutation_momentum, ← neg_smul, ← neg_mul, comp_smul,
    comp_id, ← Finset.smul_sum, sum_smul]

private lemma positionDotMomentum_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅positionDotMomentum d, 𝐩[i]⁆ = (I * ℏ) • 𝐩[i] := by
  trans ∑ j, ⁅𝐱[j], 𝐩[i]⁆ ∘L 𝐩[j]
  · simp [positionDotMomentum, sum_lie, leibniz_lie]
  simp_rw [position_commutation_momentum, smul_comp, id_comp, ← Finset.smul_sum, symm _ i, sum_smul]

private lemma positionDotMomentum_commutation_momentumSqr (d : ℕ) :
    ⁅positionDotMomentum d, momentumOperatorSqr (d := d)⁆ = (2 * I * ℏ) • 𝐩² := by
  simp [positionDotMomentum, sum_lie, leibniz_lie, ← lie_skew 𝐩[_] 𝐩²,
    position_commutation_momentumSqr, ← Finset.smul_sum, ← momentumOperatorSqr_eq]

private lemma positionDotMomentum_commutation_radiusRegPow (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    ⁅positionDotMomentum d, 𝐫[d,ε,s]⁆ = (-s * I * ℏ) • (𝐫[ε,s] - ε.1 ^ 2 • 𝐫[ε,s-2]) := by
  calc
    _ = ∑ i, 𝐱[i] ∘L ⁅𝐩[i], 𝐫[ε,s]⁆ := by simp [positionDotMomentum, sum_lie, leibniz_lie]
    _ = (-s * I * ℏ) • ∑ i, 𝐱[i] ∘L 𝐱[i] ∘L 𝐫[ε,s-2] := by
      simp [← lie_skew 𝐩[_] _, radiusRegPow_commutation_momentum, Finset.smul_sum,
        position_comp_radiusRegPow_commute]
    _ = (-s * I * ℏ) • (∑ i, 𝐱[i] ∘L 𝐱[i]) ∘L 𝐫[ε,s-2] := by simp [finset_sum_comp, comp_assoc]
    _ = (-s * I * ℏ) • (𝐫[ε,s] - ε.1 ^ 2 • 𝐫[ε,s-2]) := by simp [positionOperatorSqr_eq ε]

private lemma positionCompMomentumSqr_comm {d : ℕ} (i j : Fin d) :
    ⁅positionCompMomentumSqr i, positionCompMomentumSqr j⁆ = (-2 * I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
  calc
    _ = (𝐱[j] ∘L ⁅𝐱[i], 𝐩²⁆ + 𝐱[i] ∘L ⁅momentumOperatorSqr (d := d), 𝐱[j]⁆) ∘L 𝐩² := by
      simp [positionCompMomentumSqr, lie_leibniz, leibniz_lie, comp_assoc]
    _ = (2 * I * ℏ) • 𝐋[j,i] ∘L 𝐩² := by
      simp_rw [← lie_skew 𝐩² _, position_commutation_momentumSqr, comp_neg, comp_smul,
        ← sub_eq_add_neg, ← smul_sub, smul_comp, angularMomentumOperator]
    _ = (-2 * I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
      rw [angularMomentumOperator_antisymm j i, neg_comp, smul_neg, ← neg_smul, ← neg_mul,
        ← neg_mul, momentumSqr_comp_angularMomentum_commute]

private lemma positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add
    {d : ℕ} (i j : Fin d) : ⁅positionCompMomentumSqr i, positionDotMomentumCompMomentum j⁆ +
    ⁅positionDotMomentumCompMomentum i, positionCompMomentumSqr j⁆ = (-I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
  suffices ∀ k l : Fin d, ⁅positionCompMomentumSqr k, positionDotMomentumCompMomentum l⁆
      = (-I * ℏ) • (𝐱[k] ∘L 𝐩[l] - δ[k,l] • positionDotMomentum d) ∘L 𝐩² by
    nth_rw 2 [← lie_skew]
    simp_rw [this, ← sub_eq_add_neg, ← smul_sub, ← sub_comp, symm j i, sub_sub_sub_cancel_right,
      momentumSqr_comp_angularMomentum_commute, angularMomentumOperator]
  intro k l
  calc
    _ = (positionDotMomentum d) ∘L ⁅𝐱[k], 𝐩[l]⁆ ∘L 𝐩²
        + 𝐱[k] ∘L ⁅momentumOperatorSqr (d := d), positionDotMomentum d⁆ ∘L 𝐩[l]
        + ⁅𝐱[k], positionDotMomentum d⁆ ∘L 𝐩² ∘L 𝐩[l] := by
      simp [positionCompMomentumSqr, positionDotMomentumCompMomentum, lie_leibniz, leibniz_lie,
        add_assoc, comp_assoc]
    _ = (positionDotMomentum d) ∘L ⁅𝐱[k], 𝐩[l]⁆ ∘L 𝐩² + (-I * ℏ) • 𝐱[k] ∘L 𝐩[l] ∘L 𝐩² := by
      simp only [← lie_skew _ (positionDotMomentum d), positionDotMomentum_commutation_position,
        positionDotMomentum_commutation_momentumSqr, momentumSqr_comp_momentum_commute,
        ← neg_smul, ← neg_mul, smul_comp, comp_smul, add_assoc, ← add_smul]
      ring_nf
    _ = (-I * ℏ) • (𝐱[k] ∘L 𝐩[l] - δ[k,l] • positionDotMomentum d) ∘L 𝐩² := by
      simp_rw [add_comm, position_commutation_momentum, sub_comp, smul_sub, smul_comp, comp_smul,
        id_comp, sub_eq_add_neg, ← neg_smul, neg_mul, neg_neg, comp_assoc]

private lemma positionDotMomentumCompMomentum_comm {d : ℕ} (i j : Fin d) :
    ⁅positionDotMomentumCompMomentum i, positionDotMomentumCompMomentum j⁆ = 0 := by
  simp [positionDotMomentumCompMomentum, lie_leibniz, leibniz_lie, momentum_comp_commute,
    ← lie_skew 𝐩[_] (positionDotMomentum d), positionDotMomentum_commutation_momentum, comp_assoc]

private lemma positionCompMomentumSqr_comm_constMomentum_add {d : ℕ} (i j : Fin d) :
    ⁅positionCompMomentumSqr i, constMomentum j⁆ +
    ⁅constMomentum i, positionCompMomentumSqr j⁆ = 0 := by
  nth_rw 2 [← lie_skew]
  simp [positionCompMomentumSqr, constMomentum, leibniz_lie, position_commutation_momentum, symm j]

private lemma positionDotMomentumCompMomentum_comm_constMomentum_add {d : ℕ} (i j : Fin d) :
    ⁅positionDotMomentumCompMomentum i, constMomentum j⁆ +
    ⁅constMomentum i, positionDotMomentumCompMomentum j⁆ = 0 := by
  nth_rw 2 [← lie_skew]
  simp [positionDotMomentumCompMomentum, constMomentum, leibniz_lie,
    positionDotMomentum_commutation_momentum, momentum_comp_commute]

private lemma constMomentum_comm {d : ℕ} (i j : Fin d) :
    ⁅constMomentum i, constMomentum j⁆ = 0 := by
  simp [constMomentum]

private lemma positionCompMomentumSqr_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) : ⁅positionCompMomentumSqr i, constRadiusRegInvCompPosition H ε j⁆
    + ⁅constRadiusRegInvCompPosition H ε i, positionCompMomentumSqr j⁆
    = (-2 * I * ℏ * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐋[i,j] := by
  let A := ⁅momentumOperatorSqr (d := H.d), radiusRegPowOperator (d := H.d) ε (-1)⁆
  have hA : 𝐱[i] ∘L A ∘L 𝐱[j] = 𝐱[j] ∘L A ∘L 𝐱[i] := by
    suffices A = (2 * I * ℏ) • 𝐫[ε,-3] ∘L positionDotMomentum H.d
        + ((H.d - 3) * ℏ ^ 2 : ℝ) • 𝐫[ε,-3] + (3 * ε.1 ^ 2 * ℏ ^ 2) • 𝐫[ε,-5] by
      simp_rw [this, add_comp, comp_add, smul_comp, comp_smul, ← comp_assoc,
        position_comp_radiusRegPow_commute, comp_assoc,
        comp_eq_comp_add_commute (positionDotMomentum _), positionDotMomentum_commutation_position,
        comp_add, comp_smul, ← comp_assoc 𝐱[_] 𝐱[_] _, position_comp_commute j i]
    simp_rw [A, ← lie_skew 𝐩² _, radiusRegPow_commutation_momentumSqr, neg_sub, ← sub_sub,
      positionDotMomentum, sub_eq_add_neg, ← neg_smul, ← neg_mul, neg_neg, ofReal_neg, ofReal_one,
      ← add_rotate]
    ring_nf
  let B (i : Fin H.d) := ⁅momentumOperatorSqr (d := H.d), 𝐱[i]⁆
  have hB (k : Fin H.d) : B k = (-2 * I * ℏ) • 𝐩[k] := by
    simp [B, ← lie_skew 𝐩² _, position_commutation_momentumSqr]
  calc
    _ = (H.m * H.k) • (𝐫[ε,-1] ∘L 𝐱[i] ∘L B j + 𝐱[i] ∘L A ∘L 𝐱[j]
        - (𝐫[ε,-1] ∘L 𝐱[j] ∘L B i + 𝐱[j] ∘L A ∘L 𝐱[i])) := by
      nth_rw 2 [← lie_skew]
      simp_rw [← sub_eq_add_neg, positionCompMomentumSqr, constRadiusRegInvCompPosition, lie_smul,
        ← smul_sub, lie_leibniz, leibniz_lie, ← sub_sub]
      simp [A, B, comp_assoc]
    _ = (H.m * H.k) • 𝐫[ε,-1] ∘L (𝐱[i] ∘L B j - 𝐱[j] ∘L B i) := by simp [hA]
    _ = (-2 * I * ℏ * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐋[i,j] := by
      simp_rw [hB, comp_smul, ← smul_sub, comp_smul, angularMomentumOperator, ← Complex.coe_smul,
        smul_smul, ofReal_mul]
      ring_nf

private lemma positionDotMomentumCompMomentum_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) :
    ⁅positionDotMomentumCompMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, positionDotMomentumCompMomentum j⁆ =
    (H.m * H.k * Complex.I * ℏ * ε.1 ^ 2) • 𝐫[ε,-3] ∘L 𝐋[i,j] := by
  unfold positionDotMomentumCompMomentum constRadiusRegInvCompPosition
  nth_rw 2 [← lie_skew]
  repeat rw [lie_smul, leibniz_lie, lie_leibniz, lie_leibniz]
  repeat rw [← lie_skew 𝐩[_] 𝐱[_], position_commutation_momentum]
  repeat rw [positionDotMomentum_commutation_position]
  repeat rw [← lie_skew 𝐩[_] _, radiusRegPow_commutation_momentum]
  repeat rw [positionDotMomentum_commutation_radiusRegPow]
  simp only [smul_comp, neg_comp, comp_assoc]
  rw [position_comp_commute j i, symm j i]
  unfold angularMomentumOperator
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, Complex.ofReal_neg,
    Complex.ofReal_one, neg_mul, one_mul, neg_smul, neg_neg, comp_add, sub_comp, smul_comp,
    add_comp, neg_comp, smul_add, smul_neg, neg_add_rev, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, coe_smul', coe_comp', Pi.smul_apply, Function.comp_apply,
    coe_sub', Pi.sub_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, SchwartzMap.sub_apply, Complex.ofReal_pow,
    comp_sub]
  ring_nf

private lemma constMomentum_comm_constRadiusRegInvCompPosition_add (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, constMomentum j⁆ = 0 := by
  unfold constMomentum constRadiusRegInvCompPosition
  nth_rw 2 [← lie_skew]
  repeat rw [smul_lie, lie_smul, lie_leibniz]
  repeat rw [← lie_skew 𝐩[_] _]
  repeat rw [position_commutation_momentum, radiusRegPow_commutation_momentum]
  simp only [neg_comp, smul_comp, comp_assoc]
  rw [position_comp_commute j i, symm j i]
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, Complex.ofReal_neg,
    Complex.ofReal_one, neg_mul, one_mul, neg_smul, neg_neg, smul_add, smul_neg, neg_add_rev,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul', Pi.smul_apply,
    coe_comp', Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring

private lemma constRadiusRegInvCompPosition_comm (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constRadiusRegInvCompPosition H ε i, constRadiusRegInvCompPosition H ε j⁆ = 0 := by
  simp [constRadiusRegInvCompPosition, lie_leibniz, leibniz_lie, ← lie_skew 𝐫[_,_] 𝐱[_]]

/-- `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = -iℏ 2m 𝐇(ε)𝐋ᵢⱼ` -/
lemma lrl_commutation_lrl (ε : ℝˣ) (i j : Fin H.d) : ⁅H.lrlOperator ε i, H.lrlOperator ε j⁆
    = (-2 * Complex.I * ℏ * H.m) • (H.hamiltonianReg ε) ∘L 𝐋[i,j] := by
  repeat rw [lrlOperator_eq]

  let f_x_p_sqr := positionCompMomentumSqr (d := H.d)
  let f_xdotp_p := positionDotMomentumCompMomentum (d := H.d)
  let f_const_p := constMomentum (d := H.d)
  let f_c_rinvx := constRadiusRegInvCompPosition H ε
  trans ⁅f_x_p_sqr i, f_x_p_sqr j⁆ + ⁅f_xdotp_p i, f_xdotp_p j⁆
      + ⁅f_const_p i, f_const_p j⁆ + ⁅f_c_rinvx i, f_c_rinvx j⁆
      - (⁅f_x_p_sqr i, f_xdotp_p j⁆ + ⁅f_xdotp_p i, f_x_p_sqr j⁆)
      + (⁅f_x_p_sqr i, f_const_p j⁆ + ⁅f_const_p i, f_x_p_sqr j⁆)
      - (⁅f_x_p_sqr i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_x_p_sqr j⁆)
      - (⁅f_xdotp_p i, f_const_p j⁆ + ⁅f_const_p i, f_xdotp_p j⁆)
      + (⁅f_xdotp_p i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_xdotp_p j⁆)
      - (⁅f_const_p i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_const_p j⁆)
  · unfold f_x_p_sqr f_xdotp_p f_const_p f_c_rinvx
    unfold positionCompMomentumSqr positionDotMomentumCompMomentum constMomentum
      constRadiusRegInvCompPosition positionDotMomentum
    simp only [lie_add, lie_sub, add_lie, sub_lie]
    ext ψ x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, SchwartzMap.sub_apply,
      SchwartzMap.add_apply]
    ring

  rw [positionCompMomentumSqr_comm]
  rw [positionDotMomentumCompMomentum_comm]
  rw [positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add]
  rw [positionCompMomentumSqr_comm_constMomentum_add]
  rw [positionDotMomentumCompMomentum_comm_constMomentum_add]
  rw [constMomentum_comm]
  rw [positionCompMomentumSqr_comm_constRadiusRegInvCompPosition_add H]
  rw [positionDotMomentumCompMomentum_comm_constRadiusRegInvCompPosition_add H]
  rw [constMomentum_comm_constRadiusRegInvCompPosition_add H]
  rw [constRadiusRegInvCompPosition_comm H]

  unfold hamiltonianReg
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', coe_comp', Pi.smul_apply,
    Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
    coe_sub', Pi.sub_apply, SchwartzMap.sub_apply, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_pow, ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring_nf
  simp

/-
## Hamiltonian / LRL vector commutators
-/

private lemma pSqr_comm_pL_Lp {d : ℕ} (i : Fin d) :
    ⁅momentumOperatorSqr (d := d), ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j])⁆ = 0 := by
  simp [lie_sum, lie_leibniz, ← lie_skew 𝐩² 𝐋[_,_]]

private lemma rr_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫[d,ε,-1] + (2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-3], 𝐫[ε,-1] ∘L 𝐱[i]⁆ = 0 := by
  simp [lie_leibniz, ← lie_skew 𝐫[_,_] 𝐱[_]]

private lemma pSqr_comm_rx (ε : ℝˣ) (i : Fin H.d) :
    ⁅momentumOperatorSqr (d := H.d), 𝐫[ε,-1] ∘L 𝐱[i]⁆ =
    (-2 * Complex.I * ℏ) • 𝐫[ε,-1] ∘L 𝐩[i]
    + (ℏ ^ 2 * (H.d - 3) : ℝ) • 𝐫[ε,-3] ∘L 𝐱[i]
    + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫[ε,-5] ∘L 𝐱[i]
    + (2 * Complex.I * ℏ) • 𝐫[ε,-3] ∘L (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i] := by
  rw [lie_leibniz]
  rw [← lie_skew, position_commutation_momentumSqr]
  rw [← lie_skew, radiusRegPow_commutation_momentumSqr]
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, Complex.ofReal_neg, Complex.ofReal_one,
    mul_neg, mul_one, neg_mul, neg_smul, one_mul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul', coe_comp',
    Pi.smul_apply, Function.comp_apply, coe_sub', Pi.sub_apply, coe_sum', Finset.sum_apply, map_sum,
    SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, smul_eq_mul,
    SchwartzMap.sub_apply, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_pow,
    SchwartzMap.sum_apply]
  ring_nf

private lemma rr_comm_pL_Lp {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫[d,ε,-1] + (2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-3], ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j])⁆ =
    (- Complex.I * ℏ) • (𝐫[ε,-3] +
      (3 * 2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-5]) ∘L ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j]) := by
  rw [lie_sum]
  conv_lhs =>
    enter [2, j]
    simp only [add_lie, lie_add, smul_lie, lie_leibniz]
    repeat rw [← lie_skew _ 𝐋[_,_], angularMomentum_commutation_radiusRegPow]
    repeat rw [radiusRegPow_commutation_momentum]
    simp only [neg_zero, comp_zero, zero_comp, zero_add, add_zero]
    simp only [smul_comp, comp_smul, smul_add, ← comp_assoc]
    repeat rw [comp_eq_comp_add_commute 𝐋[_,_] 𝐫[ε,_],
      angularMomentum_commutation_radiusRegPow]
    simp only [comp_assoc]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← comp_finset_sum]
  ext ψ x
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, neg_smul,
    Complex.ofReal_ofNat, smul_neg, add_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, coe_smul', coe_comp', coe_sum', Pi.smul_apply,
    Function.comp_apply, Finset.sum_apply, map_sum, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, comp_add, add_comp, smul_comp,
    smul_add]
  ring_nf

private lemma xL_Lx_eq {d : ℕ} (ε : ℝˣ) (i : Fin d) : ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j]) =
    (2 : ℝ) • (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i]
    - (2 : ℝ) • 𝐫[ε,2] ∘L 𝐩[i] + (2 * ε.1 ^ 2) • 𝐩[i] - (Complex.I * ℏ * (d - 3)) • 𝐱[i] := by
  conv_lhs =>
    enter [2, j]
    calc
      _ = 𝐱[j] ∘L (𝐱[i] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[i])
          + (𝐱[i] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[i]) ∘L 𝐱[j] := rfl
      _ = 𝐱[j] ∘L 𝐱[i] ∘L 𝐩[j] + 𝐱[i] ∘L 𝐩[j] ∘L 𝐱[j]
          - 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i] - 𝐱[j] ∘L 𝐩[i] ∘L 𝐱[j] := by
        rw [comp_sub, sub_comp]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', Pi.sub_apply,
          Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.sub_apply]
        ring
      _ = 𝐱[j] ∘L 𝐩[j] ∘L 𝐱[i] + 𝐱[i] ∘L 𝐱[j] ∘L 𝐩[j] - (2 : ℝ) • 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i]
          + (2 * Complex.I * ℏ) • δ[i,j] • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐩[j], position_commutation_momentum]
        rw [comp_eq_comp_sub_commute 𝐩[i] 𝐱[j], position_commutation_momentum]
        rw [comp_eq_comp_add_commute 𝐱[j] 𝐩[j], position_commutation_momentum]
        rw [symm j i, eq_one_of_same]
        ext
        simp only [nsmul_eq_mul, comp_add, comp_smulₛₗ, RingHom.id_apply, comp_sub, coe_sub',
          coe_comp', coe_smul', coe_mul, coe_id', CompTriple.comp_eq, Pi.sub_apply,
          ContinuousLinearMap.add_apply, Function.comp_apply, Pi.smul_apply, natCast_apply,
          map_smul_of_tower, SchwartzMap.sub_apply, SchwartzMap.add_apply, positionOperator_apply,
          momentumOperator_apply, neg_mul, mul_neg, SchwartzMap.smul_apply, smul_eq_mul,
          sub_neg_eq_add, one_smul, comp_id, smul_neg, real_smul, ofReal_ofNat]
        ring
      _ = 𝐱[j] ∘L 𝐩[j] ∘L 𝐱[i] + 𝐱[j] ∘L 𝐱[i] ∘L 𝐩[j] - (2 : ℝ) • 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i]
          + (2 * Complex.I * ℏ) • δ[i,j] • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        nth_rw 2 [← comp_assoc]
        rw [position_comp_commute i j, comp_assoc]
      _ = (2 : ℝ) • (𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i] - (2 : ℝ) • (𝐱[j] ∘L 𝐱[j]) ∘L 𝐩[i]
          + (3 * Complex.I * ℏ) • δ[i,j] • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐩[j], position_commutation_momentum]
        ext
        simp only [nsmul_eq_mul, comp_add, comp_smulₛₗ, RingHom.id_apply, coe_sub', coe_smul',
          Pi.sub_apply, ContinuousLinearMap.add_apply, coe_comp', Function.comp_apply, coe_mul,
          coe_id', CompTriple.comp_eq, Pi.smul_apply, natCast_apply, map_smul_of_tower,
          SchwartzMap.sub_apply, SchwartzMap.add_apply, positionOperator_apply,
          momentumOperator_apply, neg_mul, mul_neg, SchwartzMap.smul_apply, smul_eq_mul, smul_neg,
          real_smul, ofReal_ofNat, sub_neg_eq_add, sub_left_inj]
        ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← finset_sum_comp]
  rw [positionOperatorSqr_eq ε, sub_comp, smul_comp, sum_smul, id_comp]
  simp only [smul_sub, ← sub_add, smul_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [sub_eq_add_neg, add_assoc, ← neg_smul, ← add_smul]
  congr
  ring

/-- `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏkε²(¾𝐫(ε)⁻⁵(𝐱ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐱ⱼ) + 3iℏ/2 𝐫(ε)⁻⁵𝐱ᵢ + 𝐫(ε)⁻³𝐩ᵢ)` -/
lemma hamiltonianReg_commutation_lrl (ε : ℝˣ) (i : Fin H.d) :
    ⁅H.hamiltonianReg ε, H.lrlOperator ε i⁆ = (Complex.I * ℏ * H.k * ε.1 ^ 2) •
    ((3 * 4⁻¹ : ℝ) • 𝐫[ε,-5] ∘L ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j])
      + (3 * 2⁻¹ * Complex.I * ℏ) • 𝐫[ε,-5] ∘L 𝐱[i] + 𝐫[ε,-3] ∘L 𝐩[i]) := by
  unfold hamiltonianReg lrlOperator
  rw [sub_lie, lie_sub, lie_sub]
  simp only [lie_smul, smul_lie]

  rw [pSqr_comm_pL_Lp]
  rw [rr_comm_rx]
  rw [pSqr_comm_rx]
  rw [rr_comm_pL_Lp]
  rw [xL_Lx_eq ε]

  simp only [smul_zero, sub_zero, zero_sub, smul_smul, smul_add, smul_sub, comp_smul, smul_comp,
    add_comp, comp_sub, comp_add]
  simp only [← comp_assoc, radiusRegPowOperator_comp_eq]
  rw [comp_assoc]
  field_simp
  rw [← sub_eq_zero]

  ext ψ x
  simp only [neg_smul, smul_neg, neg_add_rev, neg_neg, Complex.I_sq, neg_mul, one_mul, coe_sub',
    Pi.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul',
    coe_comp', coe_sum', Pi.smul_apply, Function.comp_apply, Finset.sum_apply, map_sum,
    SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    SchwartzMap.sum_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring_nf
  rw [Complex.I_sq]
  simp

/-

## LRL vector squared

To compute `𝐀(ε)²` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the first term and
  `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the second.
- Expand out to nine terms: one is a triple sum, two are double sums and the rest are single sums.
- Compute each term, symmetrizing the sums (see `sum_symmetrize` and `sum_symmetrize'`).
- Collect terms.

-/

private lemma sum_symmetrize (f : Fin H.d → Fin H.d → 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ)) :
    ∑ i, ∑ j, f i j = (2 : ℂ)⁻¹ • ∑ i, ∑ j, (f i j + f j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  ext ψ x
  rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.add_apply,
    SchwartzMap.add_apply, smul_eq_mul]
  ring

private lemma sum_symmetrize'
    (f : Fin H.d → Fin H.d → Fin H.d → 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ)) :
    ∑ i, ∑ j, ∑ k, f i j k = (2 : ℂ)⁻¹ • ∑ i, ∑ k, ∑ j, (f i j k + f k j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  conv_rhs =>
    enter [2, 1, 2, i]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, 2, 2, i]
    rw [Finset.sum_comm]
  ext ψ x
  rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.add_apply,
    SchwartzMap.add_apply, smul_eq_mul]
  ring

private lemma sum_Lpp_zero : ∑ i : Fin H.d, ∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[i] = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i, neg_comp, add_neg_cancel]
  simp

private lemma sum_ppL_zero : ∑ i : Fin H.d, ∑ j, 𝐩[i] ∘L 𝐩[j] ∘L 𝐋[i,j] = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← comp_assoc, ← comp_assoc]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i, comp_neg, add_neg_cancel]
  simp

private lemma sum_LppL : ∑ i : Fin H.d, ∑ j, ∑ k, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐋[i,k]
    = 𝐩² ∘L 𝐋² := by
  -- Apply a particular symmetrization to the triple sum
  rw [sum_symmetrize']
  conv_lhs =>
    enter [2, 2, i, 2, j, 2, k]
    rw [angularMomentumOperator_antisymm j i]
    repeat rw [comp_neg]
    repeat rw [← comp_assoc]
    rw [← sub_eq_add_neg, ← sub_comp]
    enter [1]
    unfold angularMomentumOperator
    calc
      _ = 𝐱[i] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[j] - 𝐱[k] ∘L 𝐩[i] ∘L 𝐩[k] ∘L 𝐩[j]
          - 𝐱[j] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[i] + 𝐱[k] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐩[i] := by
        simp only [sub_comp, comp_assoc, sub_add]

      _ = 𝐱[i] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[i] := by
        nth_rw 2 [momentum_comp_commute k j]
        nth_rw 2 [momentum_comp_commute k i]
        nth_rw 4 [← comp_assoc]
        rw [momentum_comp_commute i j, comp_assoc]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', Pi.sub_apply,
          Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.sub_apply]
        ring

  -- Back out of inner sum
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← finset_sum_comp, Finset.sum_sub_distrib, ← comp_finset_sum, ← comp_finset_sum]
    simp only [← comp_assoc, ← finset_sum_comp]
    rw [← momentumOperatorSqr]
    repeat rw [comp_eq_comp_add_commute 𝐱[_] 𝐩², position_commutation_momentumSqr, add_comp,
      smul_comp, comp_assoc]
    rw [momentum_comp_commute j i]
    rw [add_sub_add_right_eq_sub]
    rw [← comp_sub, ← angularMomentumOperator, comp_assoc]

  simp only [← comp_finset_sum]
  rw [← comp_smul, ← angularMomentumOperatorSqr]

private lemma sum_Lprx (ε : ℝˣ) :
    ∑ i : Fin H.d, ∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐫[ε,-1] ∘L 𝐱[i] = 𝐫[ε,-1] ∘L 𝐋² := by
  simp only [comp_eq_comp_sub_commute 𝐫[ε,-1] 𝐱[_], position_commutation_radiusRegPow,
    sub_zero]
  simp only [← comp_assoc, ← finset_sum_comp _ 𝐫[ε,-1]]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [1, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, neg_comp, neg_comp, ← sub_eq_add_neg]
    rw [comp_assoc, comp_assoc, ← comp_sub]
    repeat rw [comp_eq_comp_sub_commute 𝐩[_] 𝐱[_], position_commutation_momentum]
    rw [symm j i, sub_sub_sub_cancel_right]
    rw [← angularMomentumOperator]
  rw [← angularMomentumOperatorSqr, ← sub_eq_zero]
  exact angularMomentumSqr_commutation_radiusRegPow ε _

private lemma sum_rxpL (ε : ℝˣ) :
    ∑ i : Fin H.d, ∑ j, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[j] ∘L 𝐋[i,j] = 𝐫[ε,-1] ∘L 𝐋² := by
  simp only [← comp_finset_sum 𝐫[ε,-1]]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, comp_neg, comp_neg, ← sub_eq_add_neg]
    rw [← comp_assoc, ← comp_assoc, ← sub_comp, ← angularMomentumOperator]
  rw [← angularMomentumOperatorSqr]

private lemma sum_prx (d : ℕ) (ε : ℝˣ) : ∑ i : Fin d, 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] =
    𝐫[ε,-1] ∘L ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i] - (Complex.I * ℏ * (d - 1)) • 𝐫[ε,-1]
    - (Complex.I * ℏ * ε.1 ^ 2) • 𝐫[ε,-3] := by
  conv_lhs =>
    enter [2, i]
    rw [← comp_assoc, comp_eq_comp_sub_commute 𝐩[_] 𝐫[ε,-1], radiusRegPow_commutation_momentum]
    rw [sub_comp, smul_comp, comp_assoc, comp_assoc]
    rw [comp_eq_comp_sub_commute 𝐩[_] 𝐱[_], position_commutation_momentum]
    rw [eq_one_of_same]
    rw [comp_sub, comp_smul, one_smul, comp_id]
  repeat rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← comp_finset_sum]
  rw [positionOperatorSqr_eq, comp_sub, radiusRegPowOperator_comp_eq, comp_smul]

  ext ψ x
  simp only [ContinuousLinearMap.sub_apply, SchwartzMap.sub_apply, ContinuousLinearMap.smul_apply,
    SchwartzMap.smul_apply, ContinuousLinearMap.sum_apply, SchwartzMap.sum_apply]
  simp only [coe_comp', coe_sum', Function.comp_apply, Finset.sum_apply, map_sum,
    SchwartzMap.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
    sub_add_cancel, Complex.real_smul, Complex.ofReal_pow, sub_neg_eq_add]
  ring_nf
  congr

private lemma sum_rxp (d : ℕ) (ε : ℝˣ) : ∑ i : Fin d, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i] =
    𝐫[ε,-1] ∘L ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i] := by rw [comp_finset_sum]

private lemma sum_rxrx (d : ℕ) (ε : ℝˣ) : ∑ i, 𝐫[d,ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] =
    1 - (ε.1 ^ 2) • 𝐫[ε,-2] := by
  conv_lhs =>
    enter [2, i]
    calc
      _ = 𝐫[d,ε,-1] ∘L 𝐫[d,ε,-1] ∘L 𝐱[i] ∘L 𝐱[i] := by
        nth_rw 2 [← comp_assoc]
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐫[d,ε,-1], position_commutation_radiusRegPow,
          add_zero, comp_assoc]
      _ = 𝐫[d,ε,-2] ∘L 𝐱[i] ∘L 𝐱[i] := by
        rw [← comp_assoc, radiusRegPowOperator_comp_eq]
        congr
        ring
  rw [← comp_finset_sum, positionOperatorSqr_eq, comp_sub, comp_smul,
    radiusRegPowOperator_comp_eq, neg_add_cancel, radiusRegPowOperator_zero]
  congr

/-- The square of the (regularized) LRL vector operator is related to the (regularized) Hamiltonian
  `𝐇(ε)` of the hydrogen atom, square of the angular momentum `𝐋²` and powers of `𝐫(ε)` as
  `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² - m²k²ε²𝐫(ε)⁻² + mkε²𝐫(ε)⁻³(𝐋² + ¼ℏ²(d-1)(d-3))`. -/
lemma lrlOperatorSqr_eq (ε : ℝˣ) : H.lrlOperatorSqr ε =
    (2 * H.m) • (H.hamiltonianReg ε) ∘L
      (𝐋² + (4⁻¹ * ℏ ^ 2 * (H.d - 1) ^ 2 : ℝ) • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ))
    + (H.m * H.k) ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ)
    - ((H.m * H.k) ^ 2 * ε ^ 2) • 𝐫[ε,-2]
    + (H.m * H.k * ε ^ 2) • 𝐫[ε,-3] ∘L
      (𝐋² + (4⁻¹ * ℏ^2 * (H.d - 1) * (H.d - 3) : ℝ) •
      ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ)) := by
  unfold lrlOperatorSqr

  let a := (2⁻¹ * Complex.I * ℏ * (H.d - 1))

  -- Replace the two copies of `𝐀(ε)` in different ways and expand to nine terms
  conv_lhs =>
    enter [2, i, 1]
    rw [lrlOperator_eq']
  conv_lhs =>
    enter [2, i]
    rw [lrlOperator_eq'']
    calc
      _ = (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - a • (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L 𝐩[i]
          + a • 𝐩[i] ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - (a * a) • 𝐩[i] ∘L 𝐩[i]
          - (H.m * H.k) • (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - (a * H.m * H.k) • 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          + (a * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i]
          + (H.m * H.k) ^ 2 • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] := by
        simp only [comp_sub, add_comp, sub_comp, comp_smul, smul_comp]
        ext ψ x
        simp only [coe_sub', coe_smul', coe_comp', coe_sum', Pi.sub_apply, Function.comp_apply,
          ContinuousLinearMap.add_apply, Finset.sum_apply, Pi.smul_apply, SchwartzMap.sub_apply,
          SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
      _ = ∑ j, ∑ k, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐋[i,k]
          - a • (∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[i])
          + a • (∑ k, 𝐩[i] ∘L 𝐩[k] ∘L 𝐋[i,k])
          - (a * a) • 𝐩[i] ∘L 𝐩[i]
          - (H.m * H.k) • (∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐫[ε,-1] ∘L 𝐱[i])
          - (H.m * H.k) • (∑ k, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[k] ∘L 𝐋[i,k])
          - (a * H.m * H.k) • 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          + (a * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i]
          + (H.m * H.k) ^ 2 • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] := by
        repeat rw [finset_sum_comp, comp_finset_sum]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_smul', coe_comp', coe_sum',
          Pi.sub_apply, Finset.sum_apply, Function.comp_apply, map_sum, Pi.smul_apply,
          SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.sum_apply, smul_eq_mul,
          SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]

  -- Split the outer sum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]

  rw [sum_LppL] -- ∑∑∑ LppL = p²L²
  rw [sum_Lpp_zero, smul_zero] -- ∑∑ Lpp = 0
  rw [sum_ppL_zero, smul_zero] -- ∑∑ ppL = 0
  rw [← momentumOperatorSqr] -- ∑ pp = p²
  rw [sum_Lprx] -- ∑∑ Lpr⁻¹x = r⁻¹L²
  rw [sum_rxpL] -- ∑∑ r⁻¹xpL = r⁻¹L²
  rw [sum_prx] -- ∑ pr⁻¹x = r⁻¹ ∑ xp - iℏ(d-1)r⁻¹ - iℏε²r⁻³
  rw [sum_rxp] -- ∑ r⁻¹xp = r⁻¹ ∑ xp
  rw [sum_rxrx] -- ∑ r⁻¹xr⁻¹x = 1 - ε²r⁻²

  unfold a hamiltonianReg
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', coe_smul', SchwartzMap.add_apply,
    Pi.sub_apply, Function.comp_apply, Pi.smul_apply, SchwartzMap.sub_apply, smul_eq_mul,
    SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring_nf
  rw [Complex.I_sq]
  simp only [neg_mul, one_mul, one_div, sub_neg_eq_add, Complex.ofReal_mul, Complex.ofReal_pow,
    coe_id', id_eq, Complex.ofReal_inv, Complex.ofReal_ofNat, map_add, map_smul_of_tower,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_sub, radiusRegPowOperator_apply, one_apply, ne_eq,
    not_false_eq_true, Complex.ofReal_eq_zero, m_ne_zero, mul_inv_cancel_left₀]
  ring

end
end HydrogenAtom
end QuantumMechanics
