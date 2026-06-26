/-
Copyright (c) 2025 Fabio Anza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitch Scheffer, Fabio Anza
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real -- for Real.rpow_def_of_pos

/-!
# Ideal gas: basic entropy and adiabatic relations

In this module we formalize a simple thermodynamic model of a monophase
ideal gas. We:

* Define the entropy
    S(U,V,N) = N s₀ + N R (c \log(U/U₀) + \log(V/V₀) - (c+1)\log(N/N₀)),
* Prove equivalent formulations of the adiabatic relation for two states
  (U_a, V_a) and (U_b, V_b) at fixed N:

  1. c \log(U_a/U_b) + \log(V_a/V_b) = 0,
  2. (U_a/U_b)^c (V_a/V_b) = 1,
  3. U_a^c V_a = U_b^c V_b (the latter follows from (2)).
-/

@[expose] public section

open Real

noncomputable section

/-- Entropy of a monophase ideal gas:
    S(U,V,N) = N s0 + N R (c log(U/U0) + log(V/V0) - (c+1) log(N/N0)). -/
def entropy
    (c R s0 U0 V0 N0 : ℝ) (U V N : ℝ) : ℝ :=
  N * s0 +
    N * R *
      (c * log (U / U0) +
        log (V / V0) -
        (c + 1) * log (N / N0))

/-- Adiabatic relation in logarithmic form:
    If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed,
    then c * log (Ua/Ub) + log (Va/Vb) = 0.
-/
theorem adiabatic_relation_log
    {s0 U0 V0 N0 c R : ℝ}
    {Ua Ub Va Vb N : ℝ}
    (hUa : 0 < Ua) (hUb : 0 < Ub)
    (hVa : 0 < Va) (hVb : 0 < Vb)
    (hN : 0 < N)
    (hU0 : 0 < U0) (hV0 : 0 < V0)
    (hR : 0 < R)
    (hS :
      entropy c R s0 U0 V0 N0 Ua Va N =
      entropy c R s0 U0 V0 N0 Ub Vb N) :
    c * log (Ua / Ub) + log (Va / Vb) = 0 := by
  -- Unfold the entropy and expand every `log (x / y)` into `log x - log y`,
  -- so both `hS` and the goal become linear in the individual logarithms.
  unfold entropy at hS
  rw [Real.log_div hUa.ne' hU0.ne', Real.log_div hUb.ne' hU0.ne',
      Real.log_div hVa.ne' hV0.ne', Real.log_div hVb.ne' hV0.ne'] at hS
  rw [Real.log_div hUa.ne' hUb.ne', Real.log_div hVa.ne' hVb.ne']
  -- The difference of the two entropies is `N * R` times the goal, so the
  -- goal is exactly the second factor of a vanishing product.
  have key : N * R * (c * (log Ua - log Ub) + (log Va - log Vb)) = 0 := by
    linear_combination hS
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hN.ne' hR.ne')

/-- Adiabatic relation in product form:
    If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed,
    then (Ua/Ub)^c * (Va/Vb) = 1.
-/

theorem adiabatic_relation_UaUbVaVb
    {s0 U0 V0 N0 c R : ℝ}
    {Ua Ub Va Vb N : ℝ}
    (hUa : 0 < Ua) (hUb : 0 < Ub)
    (hVa : 0 < Va) (hVb : 0 < Vb)
    (hN : 0 < N)
    (hU0 : 0 < U0) (hV0 : 0 < V0)
    (hR : 0 < R)
    (hS :
      entropy c R s0 U0 V0 N0 Ua Va N =
      entropy c R s0 U0 V0 N0 Ub Vb N) :
    (Real.rpow (Ua / Ub) c) * (Va / Vb) = 1 := by
    have hlog := adiabatic_relation_log
      (Ua := Ua) (Ub := Ub) (Va := Va) (Vb := Vb) (N := N)
      hUa hUb hVa hVb hN hU0 hV0 hR hS

    have hUaUb_pos : 0 < Ua / Ub := div_pos hUa hUb
    have hVaVb_pos : 0 < Va / Vb := div_pos hVa hVb

      -- exponentiate both sides and rewrite with `rpow`
    have h := congrArg Real.exp hlog
    have h' :
        Real.exp (c * log (Ua / Ub) + log (Va / Vb)) = 1 := by
      simpa using h

    -- use `exp_add` and `exp_log` / `rpow_def_of_pos` to rewrite
    have hx :
        Real.exp (c * log (Ua / Ub)) = (Ua / Ub) ^ c := by
      -- rpow_def_of_pos: x^y = exp (y * log x) for x>0
      simp [Real.rpow_def_of_pos hUaUb_pos, mul_comm]

    have hy :
        Real.exp (log (Va / Vb)) = Va / Vb := by
      have : Va / Vb ≠ 0 := ne_of_gt hVaVb_pos
      simpa using Real.exp_log hVaVb_pos

    -- now simplify the LHS of h'
    have :
        (Ua / Ub) ^ c * (Va / Vb) = 1 := by
      have := h'
      -- rewrite LHS using `exp_add`, `hx`, `hy`
      simpa [Real.exp_add, hx, hy, mul_comm, mul_left_comm, mul_assoc] using this

    exact this
