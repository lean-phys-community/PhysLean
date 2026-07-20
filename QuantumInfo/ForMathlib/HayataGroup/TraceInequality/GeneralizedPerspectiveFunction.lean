/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.JensenOperatorInequality
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem

@[expose] public section

namespace GeneralizedPerspectiveFunction

universe u

open LownerHeinzTheorem
open JensenOperatorInequality

section Convexity

variable {E F G : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]
variable [Preorder G] [AddCommMonoid G] [Module ℝ G]

/-- Joint convexity of a two-variable map on prescribed domains in each argument. -/
def JointlyConvexOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂

/-- Joint convexity of a two-variable map without domain restrictions. -/
def JointlyConvex (Φ : E → F → G) : Prop :=
  JointlyConvexOn (Set.univ : Set E) (Set.univ : Set F) Φ

/-- Joint concavity of a two-variable map on prescribed domains in each argument. -/
def JointlyConcaveOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
      ≤ Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)

/-- Joint concavity of a two-variable map without domain restrictions. -/
def JointlyConcave (Φ : E → F → G) : Prop :=
  JointlyConcaveOn (Set.univ : Set E) (Set.univ : Set F) Φ

end Convexity

section Definition

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `h(B)^(1/2)` defined by real continuous functional calculus. -/
noncomputable def hSqrt (h : ℝ → ℝ) (B : L ℋ) : L ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) B

/-- The operator `h(B)^(-1/2)` defined by real continuous functional calculus. -/
noncomputable def hInvSqrt (h : ℝ → ℝ) (B : L ℋ) : L ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) B

/--
The generalized perspective function
`(fΔh)(A, B) = h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2)`.

This definition is intended to be used when `A` is Hermitian and `h(B)` is positive/invertible.
-/
noncomputable def GeneralizedPerspective (f h : ℝ → ℝ) (A B : L ℋ) : L ℋ :=
  hSqrt h B * cfcR f (hInvSqrt h B * A * hInvSqrt h B) * hSqrt h B

/-- Infix notation for generalized perspective: `(f Δ h) A B = GeneralizedPerspective f h A B`. -/
scoped infixl:70 " Δ " => GeneralizedPerspective

end Definition

section Theorem25Forward

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- Positive semidefinite operators. -/
def psdSet : Set (L ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ici (0 : ℝ)}

/-- Strictly positive operators. -/
def pdSet : Set (L ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)}

private lemma spectrum_convexCombo_Ioi {A B : L ℋ} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  have hC : IsSelfAdjoint ((1 - t) • A + t • B) :=
    ((IsSelfAdjoint.all (1 - t)).smul hA).add ((IsSelfAdjoint.all t).smul hB)
  obtain ⟨rA, hrA, hrA_le⟩ := (CFC.exists_pos_algebraMap_le_iff hA).2 fun x hx => As hx
  obtain ⟨rB, hrB, hrB_le⟩ := (CFC.exists_pos_algebraMap_le_iff hB).2 fun x hx => Bs hx
  refine fun x hx => (CFC.exists_pos_algebraMap_le_iff hC).1 ⟨(1 - t) * rA + t * rB, ?_, ?_⟩ x hx
  · rcases ht1.eq_or_lt with rfl | h1t
    · simpa using hrB
    · nlinarith
  · calc algebraMap ℝ (L ℋ) ((1 - t) * rA + t * rB)
        = (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB := by
          simp [Algebra.smul_def]
      _ ≤ (1 - t) • A + t • B :=
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (by linarith))
          (smul_le_smul_of_nonneg_left hrB_le ht0)

omit [Nontrivial ℋ] in
private lemma cfcR_sq_eq {g k : ℝ → ℝ} {A : L ℋ}
    (hA : IsSelfAdjoint A)
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = 1) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = (1 : L ℋ) := by
  rw [← cfc_mul g k A hg hk, ← cfc_const_one ℝ A]
  exact cfc_congr hmul

omit [Nontrivial ℋ] in
private lemma cfcR_mul_eq {g k m : ℝ → ℝ} {A : L ℋ}
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = m x) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = cfcR (ℋ := ℋ) m A := by
  rw [← cfc_mul g k A hg hk]
  exact cfc_congr hmul

private lemma hpow_continuousOn
    (h : ℝ → ℝ) (p : ℝ)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    ContinuousOn (fun x : ℝ ↦ (h x) ^ p) (Set.Ioi (0 : ℝ)) := by
  exact hcont.rpow_const fun x hx => .inl (hpos x hx).ne'

omit [Nontrivial ℋ] in
private lemma hSqrt_selfAdjoint (h : ℝ → ℝ) (B : L ℋ) :
    IsSelfAdjoint (hSqrt (ℋ := ℋ) h B) := by
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hInvSqrt_selfAdjoint (h : ℝ → ℝ) (B : L ℋ) :
    IsSelfAdjoint (hInvSqrt (ℋ := ℋ) h B) := by
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hInvSqrt_eq_one
    {h : ℝ → ℝ} {B : L ℋ}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hInvSqrt (ℋ := ℋ) h B = (1 : L ℋ) := by
  refine cfcR_sq_eq hB ((hpow_continuousOn h _ hcont hpos).mono Bs)
    ((hpow_continuousOn h _ hcont hpos).mono Bs) fun x hx => ?_
  rw [← Real.rpow_add (hpos x (Bs hx))]
  norm_num

omit [Nontrivial ℋ] in
private lemma hInvSqrt_mul_hSqrt_eq_one
    {h : ℝ → ℝ} {B : L ℋ}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hInvSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = (1 : L ℋ) := by
  refine cfcR_sq_eq hB ((hpow_continuousOn h _ hcont hpos).mono Bs)
    ((hpow_continuousOn h _ hcont hpos).mono Bs) fun x hx => ?_
  rw [← Real.rpow_add (hpos x (Bs hx))]
  norm_num

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hSqrt_eq
    {h : ℝ → ℝ} {B : L ℋ}
    (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = cfcR (ℋ := ℋ) h B := by
  refine cfcR_mul_eq ((hpow_continuousOn h _ hcont hpos).mono Bs)
    ((hpow_continuousOn h _ hcont hpos).mono Bs) fun x hx => ?_
  rw [← Real.rpow_add (hpos x (Bs hx))]
  norm_num

omit [Nontrivial ℋ] in
private lemma conj_le_conj {X Y T : L ℋ} (hXY : X ≤ Y) (hT : IsSelfAdjoint T) :
    T * X * T ≤ T * Y * T :=
  hT.conjugate_le_conjugate hXY

set_option maxHeartbeats 800000 in
-- The generalized-perspective normalization expands several nested CFC products.
private theorem theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    {f h : ℝ → ℝ}
    (hcoreV : CondV (ℋ := ℋ) f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  rintro A₁ A₂ B₁ B₂ θ ⟨hA₁_sa, hA₁_spec⟩ ⟨hA₂_sa, hA₂_spec⟩ ⟨hB₁_sa, hB₁_spec⟩
    ⟨hB₂_sa, hB₂_spec⟩ hθ0 hθ1
  let A : L ℋ := (1 - θ) • A₁ + θ • A₂
  let B : L ℋ := (1 - θ) • B₁ + θ • B₂
  have hA₁_nonneg : (0 : L ℋ) ≤ A₁ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₁ hA₁_sa).2 fun x hx => hA₁_spec hx
  have hA₂_nonneg : (0 : L ℋ) ≤ A₂ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₂ hA₂_sa).2 fun x hx => hA₂_spec hx
  have hB_sa : IsSelfAdjoint B :=
    ((IsSelfAdjoint.all (1 - θ)).smul hB₁_sa).add ((IsSelfAdjoint.all θ).smul hB₂_sa)
  have hB_spec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_convexCombo_Ioi (ℋ := ℋ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
  have hB_conc :
      (1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂ ≤ cfcR (ℋ := ℋ) h B := by
    simpa [B, cfcR, cfc_neg, smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using
      neg_le_neg (hconc hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec)
  let S : L ℋ := hSqrt (ℋ := ℋ) h B
  let IR : L ℋ := hInvSqrt (ℋ := ℋ) h B
  let S₁ : L ℋ := hSqrt (ℋ := ℋ) h B₁
  let S₂ : L ℋ := hSqrt (ℋ := ℋ) h B₂
  let IR₁ : L ℋ := hInvSqrt (ℋ := ℋ) h B₁
  let IR₂ : L ℋ := hInvSqrt (ℋ := ℋ) h B₂
  let T₁ : L ℋ := Real.sqrt (1 - θ) • (S₁ * IR)
  let T₂ : L ℋ := Real.sqrt θ • (S₂ * IR)
  let M₁ : L ℋ := IR₁ * A₁ * IR₁
  let M₂ : L ℋ := IR₂ * A₂ * IR₂
  have hS_sa : IsSelfAdjoint S := hSqrt_selfAdjoint (ℋ := ℋ) h B
  have hIR_sa : IsSelfAdjoint IR := hInvSqrt_selfAdjoint (ℋ := ℋ) h B
  have hS₁_sa : IsSelfAdjoint S₁ := hSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hS₂_sa : IsSelfAdjoint S₂ := hSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hIR₁_sa : IsSelfAdjoint IR₁ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hIR₂_sa : IsSelfAdjoint IR₂ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hSIR : S * IR = (1 : L ℋ) := hSqrt_mul_hInvSqrt_eq_one hB_sa hB_spec hcont hpos
  have hIRS : IR * S = (1 : L ℋ) := hInvSqrt_mul_hSqrt_eq_one hB_sa hB_spec hcont hpos
  have hS₁IR₁ : S₁ * IR₁ = (1 : L ℋ) := hSqrt_mul_hInvSqrt_eq_one hB₁_sa hB₁_spec hcont hpos
  have hIR₁S₁ : IR₁ * S₁ = (1 : L ℋ) := hInvSqrt_mul_hSqrt_eq_one hB₁_sa hB₁_spec hcont hpos
  have hS₂IR₂ : S₂ * IR₂ = (1 : L ℋ) := hSqrt_mul_hInvSqrt_eq_one hB₂_sa hB₂_spec hcont hpos
  have hIR₂S₂ : IR₂ * S₂ = (1 : L ℋ) := hInvSqrt_mul_hSqrt_eq_one hB₂_sa hB₂_spec hcont hpos
  have hM₁_nonneg : (0 : L ℋ) ≤ M₁ := by
    simpa [M₁, mul_assoc] using hIR₁_sa.conjugate_nonneg hA₁_nonneg
  have hM₂_nonneg : (0 : L ℋ) ≤ M₂ := by
    simpa [M₂, mul_assoc] using hIR₂_sa.conjugate_nonneg hA₂_nonneg
  have hM₁_sa : IsSelfAdjoint M₁ := IsSelfAdjoint.of_nonneg hM₁_nonneg
  have hM₂_sa : IsSelfAdjoint M₂ := IsSelfAdjoint.of_nonneg hM₂_nonneg
  have hM₁_spec : spectrum ℝ M₁ ⊆ Set.Ici (0 : ℝ) := fun x hx =>
    spectrum_nonneg_of_nonneg hM₁_nonneg hx
  have hM₂_spec : spectrum ℝ M₂ ⊆ Set.Ici (0 : ℝ) := fun x hx =>
    spectrum_nonneg_of_nonneg hM₂_nonneg hx
  have hSS : S * S = cfcR (ℋ := ℋ) h B := hSqrt_mul_hSqrt_eq hB_spec hcont hpos
  have hSS₁ : S₁ * S₁ = cfcR (ℋ := ℋ) h B₁ := hSqrt_mul_hSqrt_eq hB₁_spec hcont hpos
  have hSS₂ : S₂ * S₂ = cfcR (ℋ := ℋ) h B₂ := hSqrt_mul_hSqrt_eq hB₂_spec hcont hpos
  have hT₁ : star T₁ * T₁ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
    rw [← hSS₁, ← Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
    simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
  have hT₂ : star T₂ * T₂ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
    rw [← hSS₂, ← Real.mul_self_sqrt hθ0]
    simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
  have hTsum : star T₁ * T₁ + star T₂ * T₂ ≤ (1 : L ℋ) := by
    calc star T₁ * T₁ + star T₂ * T₂
        = IR * ((1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂) * IR := by
          rw [hT₁, hT₂]
          simp [mul_add, add_mul, mul_assoc]
      _ ≤ IR * cfcR (ℋ := ℋ) h B * IR := conj_le_conj (ℋ := ℋ) hB_conc hIR_sa
      _ = 1 := by simp [← hSS, ← mul_assoc, hIRS, hSIR]
  have hterm₁ : star T₁ * M₁ * T₁ = (1 - θ) • (IR * A₁ * IR) := by
    have h₁ : S₁ * M₁ * S₁ = A₁ := by
      simp only [M₁, ← mul_assoc, hS₁IR₁, one_mul]
      simp [mul_assoc, hIR₁S₁]
    rw [← h₁, ← Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
    simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
  have hterm₂ : star T₂ * M₂ * T₂ = θ • (IR * A₂ * IR) := by
    have h₂ : S₂ * M₂ * S₂ = A₂ := by
      simp only [M₂, ← mul_assoc, hS₂IR₂, one_mul]
      simp [mul_assoc, hIR₂S₂]
    rw [← h₂, ← Real.mul_self_sqrt hθ0]
    simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
  have hleft_inner : star T₁ * M₁ * T₁ + star T₂ * M₂ * T₂ = IR * A * IR := by
    rw [hterm₁, hterm₂]
    simp [A, mul_add, add_mul, mul_assoc]
  have houter := conj_le_conj (hcoreV hM₁_sa hM₂_sa hM₁_spec hM₂_spec hTsum) hS_sa
  rw [hleft_inner] at houter
  have hright₁ :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S = (1 - θ) • ((f Δ h) A₁ B₁) := by
    calc S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S
        = (1 - θ) • (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
          rw [← Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
          simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) := by simp [mul_assoc, hSIR, hIRS]
      _ = (1 - θ) • ((f Δ h) A₁ B₁) := rfl
  have hright₂ :
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S = θ • ((f Δ h) A₂ B₂) := by
    calc S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S
        = θ • (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
          rw [← Real.mul_self_sqrt hθ0]
          simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) := by simp [mul_assoc, hSIR, hIRS]
      _ = θ • ((f Δ h) A₂ B₂) := rfl
  exact houter.trans_eq (by rw [mul_add, add_mul, hright₁, hright₂])

-- Restricted forward form of Theorem 2.5 on the positive cone.
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd
    {f h : ℝ → ℝ}
    (hf : CondIAll.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  exact theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    (theorem_2_5_2_i_all_imp_v (ℋ := ℋ) hf) hconc hcont hpos

-- Restricted localized forward form of Theorem 2.5 on the positive cone.
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
    {f h : ℝ → ℝ}
    (hf : CondIciAll.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  exact theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    (theorem_2_5_2_i_ici_all_imp_v (ℋ := ℋ) hf) hconc hcont hpos

omit [Nontrivial ℋ] in
private lemma generalizedPerspective_neg
    (f h : ℝ → ℝ) (A B : L ℋ) :
    ((fun x : ℝ ↦ -f x) Δ h) A B = -((f Δ h) A B) := by
  simp [GeneralizedPerspective, cfcR, cfc_neg, mul_assoc]

omit [Nontrivial ℋ] in
private lemma jointlyConvexOn_neg
    {s : Set (L ℋ)} {t : Set (L ℋ)} {Φ : L ℋ → L ℋ → L ℋ}
    (hΦ : JointlyConvexOn s t (fun A B ↦ -Φ A B)) :
    JointlyConcaveOn s t Φ := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa [add_comm] using neg_le_neg (hΦ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1)

/-- Restricted forward form of Corollary 2.6 on the positive cone. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveAll.{u} f)
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hfneg : CondIAll.{u} (fun x : ℝ ↦ -f x) :=
    ⟨fun {K} _ _ _ _ => hfconc (K := K), neg_nonpos.mpr hf0⟩
  refine jointlyConvexOn_neg (ℋ := ℋ) ?_
  simpa [generalizedPerspective_neg] using
    theorem_2_5_forward_jointlyConvexOn_psd_pd (ℋ := ℋ) hfneg hconc hcont hpos

/-- Restricted localized forward form of Corollary 2.6 on the positive cone. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hfcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hfneg : CondIciAll.{u} (fun x : ℝ ↦ -f x) :=
    ⟨fun {K} _ _ _ _ => hfconc (K := K), hfcont.neg, neg_nonpos.mpr hf0⟩
  refine jointlyConvexOn_neg (ℋ := ℋ) ?_
  simpa [generalizedPerspective_neg] using
    theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici (ℋ := ℋ) hfneg hconc hcont hpos

end Theorem25Forward

-- GeneralizedPerspectiveFunction Page 1 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- For any qudit ℋ, any A ∈ Herm(ℋ), any B ∈ Pd(ℋ),
-- any real-valued continuous function f, any positive-valued continuous function h>0,
-- (fΔh)(A,B) := h(B)^{1/2} f(h(B)^{-1/2} A h(B)^{-1/2}) h(B)^{1/2}

-- Theorem 2.5 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≤ 0, and h is a continuous function with h > 0.
-- If f is operator convex and h is operator concave,
-- then fΔh is jointly convex

end GeneralizedPerspectiveFunction

-- Corollary 2.6 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≥ 0, and h is a continuous function with h > 0.
-- If f is operator convcave and h is operator concave,
-- then fΔh is jointly concave
