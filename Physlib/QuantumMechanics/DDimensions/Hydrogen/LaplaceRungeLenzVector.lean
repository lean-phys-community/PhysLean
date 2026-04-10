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
  (2 : ℝ)⁻¹ • ∑ j, (𝐩 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩 j) - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i

/-- The square of the LRL vector operator, `𝐀(ε)² ≔ 𝐀(ε)ᵢ𝐀(ε)ᵢ`. -/
def lrlOperatorSqr (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  ∑ i, (H.lrlOperator ε i) ∘L (H.lrlOperator ε i)

/-- `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i = 𝐱 i ∘L 𝐩² - (∑ j, 𝐱 j ∘L 𝐩 j) ∘L 𝐩 i
    + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
  rw [lrlOperator, sub_left_inj] -- mk·r⁻¹x terms match exactly
  calc
    _ = (2 : ℂ)⁻¹ • ∑ j, ((𝐩 j ∘L 𝐱 i) ∘L 𝐩 j + 𝐱 i ∘L 𝐩 j ∘L 𝐩 j
        - ((𝐩 j ∘L 𝐱 j) ∘L 𝐩 i + 𝐱 j ∘L 𝐩 j ∘L 𝐩 i)) := by
      simp [angularMomentumOperator, add_sub, comp_assoc, sub_add_eq_add_sub, sub_sub,
        momentum_comp_commute, ← Complex.coe_smul]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - (I * ℏ) • δ[i,j] • 𝐩 j
        - ((2 : ℂ) • (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i - (I * ℏ) • 𝐩 i)) := by
      simp only [momentum_comp_position_eq, sub_comp, smul_comp, id_comp, sub_add_eq_add_sub,
        comp_assoc, two_smul, eq_one_of_same, one_smul]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - (2 : ℂ) • (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i
        + (I * ℏ) • 𝐩 i - (I * ℏ) • δ[i,j] • 𝐩 j) := by
      simp_rw [sub_sub_sub_comm, sub_sub_eq_add_sub]
    _ = 𝐱 i ∘L ∑ j, 𝐩 j ∘L 𝐩 j - (∑ j, 𝐱 j ∘L 𝐩 j) ∘L 𝐩 i + ((2⁻¹ * I * ℏ) • H.d • 𝐩 i
        - (2⁻¹ * I * ℏ) • 𝐩 i) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, sum_smul,
        smul_add, smul_sub, smul_smul, comp_finset_sum, finset_sum_comp, mul_assoc, add_sub_assoc]
      norm_num
  rw [momentumOperatorSqr, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← sub_smul]
  ring_nf

/-- `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐋[i,j] ∘L 𝐩 j
    + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
  rw [lrlOperator_eq, sub_left_inj, add_left_inj]
  symm
  trans ∑ j, 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - ∑ j, (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i
  · simp [angularMomentumOperator, comp_assoc, momentum_comp_commute]
  simp [← comp_finset_sum, ← finset_sum_comp, momentumOperatorSqr]

set_option backward.isDefEq.respectTransparency false in
/-- `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq'' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐩 j ∘L 𝐋[i,j]
    - (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
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
private def positionDotMomentum (d : ℕ) := ∑ i : Fin d, 𝐱 i ∘L 𝐩 i

/-- The operator `𝐱ᵢ𝐩²` on Schwartz maps. -/
private def positionCompMomentumSqr {d : ℕ} (i : Fin d) := 𝐱 i ∘L 𝐩²

/-- The operator `(𝐱ⱼ𝐩ⱼ)𝐱ᵢ` on Schwartz maps. -/
private def positionDotMomentumCompMomentum {d : ℕ} (i : Fin d) := positionDotMomentum d ∘L 𝐩 i

/-- The operator `½iℏ(d-1)𝐩ᵢ` on Schwartz maps. -/
private def constMomentum {d : ℕ} (i : Fin d) := (2⁻¹ * I * ℏ * (d - 1)) • 𝐩 i

/-- The operator `mk·𝐫(ε)⁻¹𝐱ᵢ` on Schwartz maps. -/
private def constRadiusRegInvCompPosition (ε : ℝˣ) (i : Fin H.d) := (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i

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
    ⁅positionDotMomentum d, 𝐱 i⁆ = (-I * ℏ) • 𝐱 i := by
  trans ∑ j, 𝐱 j ∘L ⁅𝐩 j, 𝐱 i⁆
  · simp [positionDotMomentum, sum_lie, leibniz_lie]
  simp_rw [← lie_skew (𝐩 _), position_commutation_momentum, ← neg_smul, ← neg_mul, comp_smul,
    comp_id, ← Finset.smul_sum, sum_smul]

private lemma positionDotMomentum_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅positionDotMomentum d, 𝐩 i⁆ = (I * ℏ) • 𝐩 i := by
  trans ∑ j, ⁅𝐱 j, 𝐩 i⁆ ∘L 𝐩 j
  · simp [positionDotMomentum, sum_lie, leibniz_lie]
  simp_rw [position_commutation_momentum, smul_comp, id_comp, ← Finset.smul_sum, symm _ i, sum_smul]

private lemma positionDotMomentum_commutation_momentumSqr (d : ℕ) :
    ⁅positionDotMomentum d, momentumOperatorSqr (d := d)⁆ = (2 * I * ℏ) • 𝐩² := by
  simp [positionDotMomentum, sum_lie, leibniz_lie, ← lie_skew (𝐩 _) 𝐩²,
    position_commutation_momentumSqr, ← Finset.smul_sum, ← momentumOperatorSqr_eq]

private lemma positionDotMomentum_commutation_radiusRegPow (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    ⁅positionDotMomentum d, 𝐫₀[d] ε s⁆ = (-s * I * ℏ) • (𝐫₀ ε s - ε.1 ^ 2 • 𝐫₀ ε (s-2)) := by
  calc
    _ = ∑ i, 𝐱 i ∘L ⁅𝐩 i, 𝐫₀ ε s⁆ := by simp [positionDotMomentum, sum_lie, leibniz_lie]
    _ = (-s * I * ℏ) • ∑ i, 𝐱 i ∘L 𝐱 i ∘L 𝐫₀ ε (s-2) := by
      simp [← lie_skew (𝐩 _), radiusRegPow_commutation_momentum, Finset.smul_sum,
        position_comp_radiusRegPow_commute]
    _ = (-s * I * ℏ) • (∑ i, 𝐱 i ∘L 𝐱 i) ∘L 𝐫₀ ε (s-2) := by simp [finset_sum_comp, comp_assoc]
    _ = (-s * I * ℏ) • (𝐫₀ ε s - ε.1 ^ 2 • 𝐫₀ ε (s-2)) := by simp [positionOperatorSqr_eq ε]

private lemma positionCompMomentumSqr_comm {d : ℕ} (i j : Fin d) :
    ⁅positionCompMomentumSqr i, positionCompMomentumSqr j⁆ = (-2 * I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
  calc
    _ = (𝐱 j ∘L ⁅𝐱 i, 𝐩²⁆ + 𝐱 i ∘L ⁅momentumOperatorSqr (d := d), 𝐱 j⁆) ∘L 𝐩² := by
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
      = (-I * ℏ) • (𝐱 k ∘L 𝐩 l - δ[k,l] • positionDotMomentum d) ∘L 𝐩² by
    nth_rw 2 [← lie_skew]
    simp_rw [this, ← sub_eq_add_neg, ← smul_sub, ← sub_comp, symm j i, sub_sub_sub_cancel_right,
      momentumSqr_comp_angularMomentum_commute, angularMomentumOperator]
  intro k l
  calc
    _ = (positionDotMomentum d) ∘L ⁅𝐱 k, 𝐩 l⁆ ∘L 𝐩²
        + 𝐱 k ∘L ⁅momentumOperatorSqr (d := d), positionDotMomentum d⁆ ∘L 𝐩 l
        + ⁅𝐱 k, positionDotMomentum d⁆ ∘L 𝐩² ∘L 𝐩 l := by
      simp [positionCompMomentumSqr, positionDotMomentumCompMomentum, lie_leibniz, leibniz_lie,
        add_assoc, comp_assoc]
    _ = (positionDotMomentum d) ∘L ⁅𝐱 k, 𝐩 l⁆ ∘L 𝐩² + (-I * ℏ) • 𝐱 k ∘L 𝐩 l ∘L 𝐩² := by
      simp only [← lie_skew _ (positionDotMomentum d), positionDotMomentum_commutation_position,
        positionDotMomentum_commutation_momentumSqr, momentumSqr_comp_momentum_commute,
        ← neg_smul, ← neg_mul, smul_comp, comp_smul, add_assoc, ← add_smul]
      ring_nf
    _ = (-I * ℏ) • (𝐱 k ∘L 𝐩 l - δ[k,l] • positionDotMomentum d) ∘L 𝐩² := by
      simp_rw [add_comm, position_commutation_momentum, sub_comp, smul_sub, smul_comp, comp_smul,
        id_comp, sub_eq_add_neg, ← neg_smul, neg_mul, neg_neg, comp_assoc]

private lemma positionDotMomentumCompMomentum_comm {d : ℕ} (i j : Fin d) :
    ⁅positionDotMomentumCompMomentum i, positionDotMomentumCompMomentum j⁆ = 0 := by
  simp [positionDotMomentumCompMomentum, lie_leibniz, leibniz_lie, momentum_comp_commute,
    ← lie_skew (𝐩 _) (positionDotMomentum d), positionDotMomentum_commutation_momentum, comp_assoc]

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

set_option backward.isDefEq.respectTransparency false in
private lemma positionCompMomentumSqr_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) : ⁅positionCompMomentumSqr i, constRadiusRegInvCompPosition H ε j⁆
    + ⁅constRadiusRegInvCompPosition H ε i, positionCompMomentumSqr j⁆
    = (-2 * I * ℏ * H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐋[i,j] := by
  let A := ⁅momentumOperatorSqr (d := H.d), radiusRegPowOperator (d := H.d) ε (-1)⁆
  have hA : 𝐱 i ∘L A ∘L 𝐱 j = 𝐱 j ∘L A ∘L 𝐱 i := by
    suffices A = (2 * I * ℏ) • 𝐫₀ ε (-3) ∘L positionDotMomentum H.d
        + ((H.d - 3) * ℏ ^ 2 : ℝ) • 𝐫₀ ε (-3) + (3 * ε.1 ^ 2 * ℏ ^ 2) • 𝐫₀ ε (-5) by
      simp_rw [this, add_comp, comp_add, smul_comp, comp_smul, ← comp_assoc,
        position_comp_radiusRegPow_commute, comp_assoc,
        comp_eq_comp_add_commute (positionDotMomentum _), positionDotMomentum_commutation_position,
        comp_add, comp_smul, ← comp_assoc (𝐱 _) (𝐱 _) _, position_comp_commute j i]
    simp_rw [A, ← lie_skew 𝐩² _, radiusRegPow_commutation_momentumSqr, neg_sub, ← sub_sub,
      positionDotMomentum, sub_eq_add_neg, ← neg_smul, ← neg_mul, neg_neg, ofReal_neg, ofReal_one,
      ← add_rotate]
    ring_nf
  let B (i : Fin H.d) := ⁅momentumOperatorSqr (d := H.d), 𝐱 i⁆
  have hB (k : Fin H.d) : B k = (-2 * I * ℏ) • 𝐩 k := by
    simp [B, ← lie_skew 𝐩² _, position_commutation_momentumSqr]
  calc
    _ = (H.m * H.k) • (𝐫₀ ε (-1) ∘L 𝐱 i ∘L B j + 𝐱 i ∘L A ∘L 𝐱 j
        - (𝐫₀ ε (-1) ∘L 𝐱 j ∘L B i + 𝐱 j ∘L A ∘L 𝐱 i)) := by
      nth_rw 2 [← lie_skew]
      simp_rw [← sub_eq_add_neg, positionCompMomentumSqr, constRadiusRegInvCompPosition, lie_smul,
        ← smul_sub, lie_leibniz, leibniz_lie, ← sub_sub]
      simp [A, B, comp_assoc]
    _ = (H.m * H.k) • 𝐫₀ ε (-1) ∘L (𝐱 i ∘L B j - 𝐱 j ∘L B i) := by simp [hA]
    _ = (-2 * I * ℏ * H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐋[i,j] := by
      simp_rw [hB, comp_smul, ← smul_sub, comp_smul, angularMomentumOperator, ← Complex.coe_smul,
        smul_smul, ofReal_mul]
      ring_nf

private lemma momentum_comm_radiusRegPow_position_symm {d : ℕ} (ε : ℝˣ) (s : ℝ) (i j : Fin d) :
    ⁅𝐩 i, 𝐫₀ ε s ∘L 𝐱 j⁆ = ⁅𝐩 j, 𝐫₀ ε s ∘L 𝐱 i⁆ := by
  simp [← lie_skew (𝐩 _), leibniz_lie, position_commutation_momentum, symm j i,
    radiusRegPow_commutation_momentum, position_comp_commute j i, comp_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma positionDotMomentumCompMomentum_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) :
    ⁅positionDotMomentumCompMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, positionDotMomentumCompMomentum j⁆ =
    (I * ℏ * H.m * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐋[i,j] := by
  suffices ∀ k, ⁅positionDotMomentum H.d, constRadiusRegInvCompPosition H ε k⁆
      = (-I * ℏ * H.m * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐱 k by
    nth_rw 2 [← lie_skew]
    simp_rw [positionDotMomentumCompMomentum, leibniz_lie, this, constRadiusRegInvCompPosition,
      lie_smul, momentum_comm_radiusRegPow_position_symm, ← sub_eq_add_neg, add_sub_add_left_eq_sub,
      smul_comp, ← smul_sub, comp_assoc, ← comp_sub, angularMomentumOperator_antisymm i j, comp_neg,
      smul_neg, neg_mul, neg_smul, angularMomentumOperator]
  intro k
  calc
    _ = (H.m * H.k) • (𝐫₀ ε (-1) ∘L ⁅positionDotMomentum H.d, 𝐱 k⁆
        + ⁅positionDotMomentum H.d, 𝐫₀ ε (-1)⁆ ∘L 𝐱 k) := by
      rw [constRadiusRegInvCompPosition, lie_smul, lie_leibniz]
    _ = -(I * ℏ) • (H.m * H.k) • (ε.1 ^ 2) • 𝐫₀ ε (-1-2) ∘L 𝐱 k := by
      simp [positionDotMomentum_commutation_position, positionDotMomentum_commutation_radiusRegPow,
        sub_comp, smul_sub, ← add_sub_assoc, smul_comm _ (I * ℏ)]
    _ = (-I * ℏ * H.m * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐱 k := by
      simp only [← Complex.coe_smul, ofReal_pow, ofReal_mul, smul_smul]
      ring_nf

set_option backward.isDefEq.respectTransparency false in
private lemma constMomentum_comm_constRadiusRegInvCompPosition_add (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, constMomentum j⁆ = 0 := by
  nth_rw 2 [← lie_skew]
  simp [constMomentum, constRadiusRegInvCompPosition, momentum_comm_radiusRegPow_position_symm]

set_option backward.isDefEq.respectTransparency false in
private lemma constRadiusRegInvCompPosition_comm (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constRadiusRegInvCompPosition H ε i, constRadiusRegInvCompPosition H ε j⁆ = 0 := by
  simp [constRadiusRegInvCompPosition, lie_leibniz, leibniz_lie, ← lie_skew (𝐫₀ _ _) (𝐱 _)]

/-- `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = (-2iℏm·𝐇(ε) + iℏmkε²·𝐫(ε)⁻³)𝐋ᵢⱼ` -/
lemma lrl_commutation_lrl (ε : ℝˣ) (i j : Fin H.d) :
    ⁅H.lrlOperator ε i, H.lrlOperator ε j⁆ = ((-2 * I * ℏ * H.m) • H.hamiltonianReg ε
    + (I * ℏ * H.m * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3)) ∘L 𝐋[i,j] := by
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
  · dsimp [f_x_p_sqr, f_xdotp_p, f_const_p, f_c_rinvx, positionCompMomentumSqr, positionDotMomentum,
      positionDotMomentumCompMomentum, constMomentum, constRadiusRegInvCompPosition]
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
  simp only [add_zero, sub_zero, hamiltonianReg, smul_sub, ← Complex.coe_smul, smul_smul,
    ← sub_smul, sub_add, sub_comp, smul_comp, ofReal_inv, ofReal_mul, ofReal_ofNat]
  ring_nf
  simp

/-
## Hamiltonian / LRL vector commutators
-/

private lemma pSqr_comm_pL_Lp {d : ℕ} (i : Fin d) :
    ⁅momentumOperatorSqr (d := d), ∑ j, (𝐩 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩 j)⁆ = 0 := by
  simp [lie_sum, lie_leibniz, ← lie_skew 𝐩² 𝐋[_,_]]

private lemma r_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) : ⁅𝐫₀[d] ε (-1), 𝐫₀ ε (-1) ∘L 𝐱 i⁆ = 0 := by
  simp [lie_leibniz, ← lie_skew (𝐫₀ _ _) (𝐱 _)]

private lemma xL_Lx_eq {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ∑ j, (𝐱 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱 j) = (2 : ℝ) • (positionDotMomentum d) ∘L 𝐱 i
    + (-I * ℏ * (d - 3)) • 𝐱 i + ((-2 : ℝ) • 𝐫₀ ε 2 ∘L 𝐩 i + (2 * ε.1 ^ 2 : ℝ) • 𝐩 i) := by
  -- Change summand
  simp_rw [angularMomentumOperator, comp_sub, sub_comp, comp_assoc, sub_add_sub_comm,
    momentum_comp_position_eq, comp_sub, comp_smul, comp_id, ← comp_assoc,
    position_comp_commute i _, ← add_sub_assoc, ← two_smul ℝ, sub_sub_eq_add_sub,
    sub_add_eq_add_sub, comp_assoc, comp_eq_comp_add_commute (𝐱 i) (𝐩 _),
    position_commutation_momentum, symm _ i, comp_add, comp_smul, smul_add, comp_id, add_assoc,
    ← Complex.coe_smul, smul_smul, ← add_smul, ← comp_assoc, eq_one_of_same, one_smul]
  -- Split/do sums
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← finset_sum_comp,
    sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    positionOperatorSqr_eq ε, sub_comp, smul_comp, id_comp, smul_sub, positionDotMomentum]
  -- Clean up coefficients
  simp_rw [add_sub_assoc, add_right_inj, smul_smul, ← sub_smul, sub_eq_add_neg, neg_add, ← neg_smul,
    ← Complex.coe_smul, smul_smul, ofReal_neg, ofReal_mul, ofReal_pow, ofReal_ofNat, neg_neg]
  ring_nf

set_option backward.isDefEq.respectTransparency false in
private lemma pSqr_comm_rx (ε : ℝˣ) (i : Fin H.d) :
    ⁅momentumOperatorSqr (d := H.d), 𝐫₀ ε (-1) ∘L 𝐱 i⁆
    = (I * ℏ) • 𝐫₀ ε (-3) ∘L ∑ j, (𝐱 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱 j)
    + ((-2 * I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐩 i + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i) := by
  trans (-2 * I * ℏ) • 𝐫₀ ε (-1) ∘L 𝐩 i
      + (2 * I * ℏ) • 𝐫₀ ε (-3) ∘L (positionDotMomentum H.d) ∘L 𝐱 i
      + (ℏ ^ 2 * (H.d - 3) : ℝ) • 𝐫₀ ε (-3) ∘L 𝐱 i + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i
  · rw [← lie_skew, positionDotMomentum]
    simp_rw [leibniz_lie, position_commutation_momentumSqr, radiusRegPow_commutation_momentumSqr,
      sub_comp, add_comp, smul_comp, comp_smul, comp_assoc, neg_add, neg_sub', neg_add,
      sub_neg_eq_add, ← neg_smul, add_assoc, ofReal_neg, ofReal_one]
    ring_nf
  rw [← add_assoc, add_left_inj, add_rotate]
  simp_rw [xL_Lx_eq ε i, comp_add, comp_smul, smul_add, ← Complex.coe_smul, smul_smul, ← comp_assoc,
    radiusRegPowOperator_comp_eq, comp_assoc, add_assoc, ← add_smul, ofReal_mul, ofReal_sub,
    ofReal_neg, ofReal_pow, ofReal_ofNat]
  ring_nf
  simp [I_sq]

private lemma r_comm_pL_Lp {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫₀[d] ε (-1), ∑ j, (𝐩 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩 j)⁆ =
    -((I * ℏ) • 𝐫₀ ε (-3) ∘L ∑ j, (𝐱 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱 j)) := by
  calc
    _ = ∑ j, (⁅𝐫₀[d] ε (-1), 𝐩 j⁆ ∘L 𝐋[i,j] + 𝐋[i,j] ∘L ⁅𝐫₀[d] ε (-1), 𝐩 j⁆) := by
      simp [lie_sum, lie_leibniz, ← lie_skew _ 𝐋[_,_]]
    _ = -((I * ℏ) • ∑ j, (𝐫₀ ε (-3) ∘L 𝐱 j ∘L 𝐋[i,j] + (𝐋[i,j] ∘L 𝐫₀ ε (-3)) ∘L 𝐱 j)) := by
      simp only [radiusRegPow_commutation_momentum, smul_comp, comp_smul, ← smul_add,
        ← Finset.smul_sum, comp_assoc, ofReal_neg, ofReal_one, ← neg_smul]
      ring_nf
    _ = -((I * ℏ) • 𝐫₀ ε (-3) ∘L ∑ j, (𝐱 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱 j)) := by
      simp_rw [angularMomentum_comp_radiusRegPow_commute, comp_assoc, ← comp_add, ← comp_finset_sum]

set_option backward.isDefEq.respectTransparency false in
/-- `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏk·ε²𝐫(ε)⁻³𝐩ᵢ - 3ℏ²k/2·ε²𝐫(ε)⁻⁵𝐱ᵢ` -/
lemma hamiltonianReg_commutation_lrl (ε : ℝˣ) (i : Fin H.d) :
    ⁅H.hamiltonianReg ε, H.lrlOperator ε i⁆ = (I * ℏ * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐩 i
    - (3 / 2 * ℏ ^ 2 * H.k * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i := by
  trans (-2⁻¹ * H.k) • (⁅momentumOperatorSqr (d := H.d), 𝐫₀ ε (-1) ∘L 𝐱 i⁆
      + ⁅radiusRegPowOperator (d := H.d) ε (-1), ∑ j, (𝐩 j ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩 j)⁆)
  · have h : H.m * H.k * (H.m⁻¹ * 2⁻¹) = 2⁻¹ * H.k := by grind [m_ne_zero]
    simp [hamiltonianReg, lrlOperator, pSqr_comm_pL_Lp, r_comm_rx, h, smul_smul, sub_eq_neg_add]
  simp_rw [pSqr_comm_rx, r_comm_pL_Lp, add_neg_cancel_comm, smul_add, sub_eq_add_neg, ← neg_smul,
    ← neg_mul, ← Complex.coe_smul, smul_smul, ofReal_mul, ofReal_neg, ofReal_inv, ofReal_div,
    ofReal_pow, ofReal_ofNat]
  ring_nf

/-

## LRL vector squared

To compute `𝐀(ε)²` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the first term and
  `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the second.
- Expand out to nine terms: one is a triple sum, two are double sums and the rest are single sums.
- Compute each term, symmetrizing the sums (see `sum_symmetrize` and `sum_symmetrize'`).
- Collect terms.

-/

private lemma sum_symmetrize {d : ℕ} (f : Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, f i j = (2 : ℂ)⁻¹ • ∑ i, ∑ j, (f i j + f j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]

private lemma sum_symmetrize' {d : ℕ}
    (f : Fin d → Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, ∑ k, f i j k = (2 : ℂ)⁻¹ • ∑ i, ∑ k, ∑ j, (f i j k + f k j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]
  congr with
  rw [Finset.sum_comm]

private lemma sum_Lpp (d : ℕ) : ∑ i : Fin d, ∑ j, 𝐋[i,j] ∘L 𝐩 j ∘L 𝐩 i = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i]
  simp

private lemma sum_ppL (d : ℕ) : ∑ i : Fin d, ∑ j, 𝐩 i ∘L 𝐩 j ∘L 𝐋[i,j] = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← comp_assoc, ← comp_assoc, angularMomentumOperator_antisymm j i, momentum_comp_commute j i]
  simp

private lemma sum_LppL (d : ℕ) :
    ∑ i : Fin d, ∑ j, ∑ k, 𝐋[i,j] ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐋[i,k] = 𝐩² ∘L 𝐋² := by
  rw [sum_symmetrize']
  conv_lhs =>
    enter [2, 2, i, 2, j, 2, k]
    calc
      _ = (𝐋[i,k] ∘L 𝐩 k ∘L 𝐩 j - 𝐋[j,k] ∘L 𝐩 k ∘L 𝐩 i) ∘L 𝐋[i,j] := by
        simp [angularMomentumOperator_antisymm j i, comp_neg, ← comp_assoc, sub_eq_add_neg]
      _ = (𝐱 i ∘L 𝐩 k ∘L 𝐩 k ∘L 𝐩 j - 𝐱 k ∘L 𝐩 i ∘L 𝐩 k ∘L 𝐩 j
          - (𝐱 j ∘L 𝐩 k ∘L 𝐩 k ∘L 𝐩 i - 𝐱 k ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐩 i)) ∘L 𝐋[i,j] := by
        simp_rw [angularMomentumOperator, sub_comp, comp_assoc]
      _ = (𝐱 i ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐩 k - 𝐱 j ∘L 𝐩 i ∘L 𝐩 k ∘L 𝐩 k) ∘L 𝐋[i,j] := by
        simp_rw [momentum_comp_commute k, ← comp_assoc (𝐩 _), momentum_comp_commute k,
          momentum_comp_commute i j, sub_sub_sub_cancel_right]
      _ = 𝐋[i,j] ∘L (𝐩 k ∘L 𝐩 k) ∘L 𝐋[i,j] := by
        simp_rw [← comp_assoc, ← sub_comp, angularMomentumOperator]
  trans (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋[i,j] ∘L 𝐩² ∘L 𝐋[i,j]
  · simp_rw [← comp_finset_sum, ← finset_sum_comp, ← comp_assoc, momentumOperatorSqr]
  simp_rw [← comp_assoc, ← momentumSqr_comp_angularMomentum_commute, comp_assoc, ← comp_finset_sum,
    ← comp_smul, angularMomentumOperatorSqr]

private lemma sum_Lprx (d : ℕ) (ε : ℝˣ) :
    ∑ i, ∑ j, 𝐋[i,j] ∘L 𝐩 j ∘L 𝐫₀[d] ε (-1) ∘L 𝐱 i = 𝐫₀ ε (-1) ∘L 𝐋² := by
  simp_rw [← position_comp_radiusRegPow_commute, ← comp_assoc, ← finset_sum_comp _ (𝐫₀ _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [1, 2, 2, i, 2, j]
    calc
      _ = 𝐋[i,j] ∘L (𝐩 j ∘L 𝐱 i - 𝐩 i ∘L 𝐱 j) := by
        simp [angularMomentumOperator_antisymm j i, comp_assoc, sub_eq_add_neg]
      _ = 𝐋[i,j] ∘L 𝐋[i,j] := by
        simp [momentum_comp_position_eq, symm j i, angularMomentumOperator]
  rw [← angularMomentumSqr_comp_radiusRegPow_commute, angularMomentumOperatorSqr]

private lemma sum_rxpL (d : ℕ) (ε : ℝˣ) :
    ∑ i, ∑ j, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐩 j ∘L 𝐋[i,j] = 𝐫₀ ε (-1) ∘L 𝐋² := by
  simp_rw [← comp_finset_sum (𝐫₀ _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, comp_neg, comp_neg, ← sub_eq_add_neg, ← comp_assoc,
      ← comp_assoc, ← sub_comp, ← angularMomentumOperator]
  rw [angularMomentumOperatorSqr]

private lemma sum_prx (d : ℕ) (ε : ℝˣ) :
    ∑ i, 𝐩 i ∘L 𝐫₀[d] ε (-1) ∘L 𝐱 i = 𝐫₀ ε (-1) ∘L ∑ i, 𝐱 i ∘L 𝐩 i
    - (I * ℏ * (d - 1)) • 𝐫₀ ε (-1) - (I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
  calc
    _ = ∑ i, (𝐫₀ ε (-1) ∘L 𝐩 i ∘L 𝐱 i + (I * ℏ) • 𝐫₀ ε (-3) ∘L 𝐱 i ∘L 𝐱 i) := by
      simp_rw [← comp_assoc, momentum_comp_radiusRegPow_eq]
      ring_nf
      simp
    _ = ∑ i, (𝐫₀ ε (-1) ∘L 𝐱 i ∘L 𝐩 i - (I * ℏ) • 𝐫₀ ε (-1)
        + (I * ℏ) • 𝐫₀ ε (-3) ∘L 𝐱 i ∘L 𝐱 i) := by simp [momentum_comp_position_eq]
    _ = 𝐫₀ ε (-1) ∘L ∑ i, 𝐱 i ∘L 𝐩 i + (-d * I * ℏ) • 𝐫₀ ε (-1)
        + (I * ℏ) • 𝐫₀ ε (-3) ∘L ∑ i, 𝐱 i ∘L 𝐱 i := by
      simp [Finset.sum_add_distrib, ← comp_finset_sum, ← Finset.smul_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc, sub_eq_add_neg]
    _ = 𝐫₀ ε (-1) ∘L ∑ i, 𝐱 i ∘L 𝐩 i
        - (I * ℏ * (d - 1)) • 𝐫₀ ε (-1) - (I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
      simp only [positionOperatorSqr_eq ε, comp_sub, comp_smul, comp_id,
        radiusRegPowOperator_comp_eq, smul_sub, ← Complex.coe_smul, ofReal_pow, smul_smul]
      ring_nf
      simp_rw [← add_sub_assoc, add_assoc, ← add_smul, sub_eq_add_neg, ← neg_smul]
      ring_nf

private lemma sum_rxp (d : ℕ) (ε : ℝˣ) :
    ∑ i, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐩 i = 𝐫₀ ε (-1) ∘L ∑ i, 𝐱 i ∘L 𝐩 i := by rw [comp_finset_sum]

set_option backward.isDefEq.respectTransparency false in
private lemma sum_rxrx (d : ℕ) (ε : ℝˣ) : ∑ i, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐫₀ ε (-1) ∘L 𝐱 i =
    ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) - (ε.1 ^ 2) • 𝐫₀ ε (-2) := by
  simp_rw [← comp_finset_sum, ← comp_assoc, position_comp_radiusRegPow_commute, comp_assoc,
    ← comp_finset_sum, ← comp_assoc, radiusRegPowOperator_comp_eq, positionOperatorSqr_eq ε]
  ring_nf
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The square of the (regularized) LRL vector operator is related to the (regularized) Hamiltonian
  `𝐇(ε)` of the hydrogen atom, square of the angular momentum `𝐋²` and powers of `𝐫(ε)` as
  `𝐀(ε)² = 2m·𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k²(𝟙 - ε²·𝐫(ε)⁻²) - ½(d-1)mkℏ²ε²𝐫(ε)⁻³`. -/
lemma lrlOperatorSqr_eq (ε : ℝˣ) : H.lrlOperatorSqr ε =
    (2 * H.m) • (H.hamiltonianReg ε) ∘L
      (𝐋² + (4⁻¹ * ℏ ^ 2 * (H.d - 1) ^ 2 : ℝ) • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ))
    + (H.m ^ 2 * H.k ^ 2) • (ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ) - ε.1 ^ 2 • 𝐫₀ ε (-2))
    - (2⁻¹ * ℏ^2 * H.m * H.k * (H.d - 1) * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
  dsimp [lrlOperatorSqr]
  conv_lhs => enter [2, i, 1]; rw [lrlOperator_eq']
  conv_lhs => enter [2, i, 2]; rw [lrlOperator_eq'']
  simp_rw [sub_eq_add_neg, ← neg_smul, add_comp, comp_add, smul_comp, comp_smul, finset_sum_comp,
    comp_finset_sum, Finset.sum_add_distrib, ← Finset.smul_sum, comp_assoc, sum_LppL, sum_Lpp,
    sum_Lprx, sum_ppL, sum_prx, sum_rxpL, sum_rxp, sum_rxrx, hamiltonianReg]
  simp only [sub_eq_add_neg, ← neg_smul, smul_zero, zero_add, add_zero, ← neg_mul, smul_smul,
    ← momentumOperatorSqr_eq, ← Complex.coe_smul, ofReal_mul, ofReal_neg, ofReal_inv, ofReal_pow,
    smul_add, ofReal_ofNat]
  ring_nf
  ext
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, Function.comp_apply, coe_comp', coe_id', smul_eq_mul, ofReal_add,
    ofReal_neg, ofReal_one, ofReal_natCast]
  grind [I_sq, m_ne_zero, mul_inv_cancel₀, ofReal_eq_zero]

end
end HydrogenAtom
end QuantumMechanics
