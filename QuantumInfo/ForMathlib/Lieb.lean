/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat

/-! Lieb's Inequality .. todo -/

@[expose] public section

variable {m n : Type*} [Fintype m] [Fintype n] {q r : ℝ}

noncomputable section
open ComplexOrder
open Classical
open RealInnerProductSpace

theorem LiebConcavity (K : Matrix n m ℂ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
  let F : (HermitianMat m ℂ × HermitianMat n ℂ) → ℝ :=
      fun (x,y) ↦ ⟪(x ^ q).conj K, y ^ r⟫;
    ConcaveOn ℝ .univ F := by
  sorry
