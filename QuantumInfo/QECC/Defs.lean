/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.CPTP

/-!
# Quantum error-correcting codes

This file defines quantum error-correcting codes (`QECC`) in a maximally general form, as a pair of
a CPTP `encoder` and a CPTP `decoder`, and develops their basic theory.

## Main definitions

A `QECC d1 i d2` encodes a logical Hilbert space on `d1` into an `i`-indexed register of qudits, each
living on the Hilbert space `d2`; that is, the physical space is `i → d2`. It consists of
* `encoder : CPTPMap d1 (i → d2)`, and
* `decoder : CPTPMap (i → d2) d1`.

The constructions on codes are:
* `QECC.identity` — the trivial code on `i → d2` (encoder = decoder = identity channel);
* `QECC.comp` — chaining two codes where the physical space of the first is the logical space of
  the second;
* `QECC.parallel` — running `j` independent copies of a code side by side, lifting `QECC d1 i d2` to
  `QECC (j → d1) (j × i) d2` (this uses the Pi-indexed Kronecker product `CPTPOp.piProd`);
* `QECC.concat` — code concatenation, where each physical qudit of the outer code is itself encoded
  by the inner code (`d1` of the inner equals `d2` of the outer). This is the outer code composed
  with the parallel construction of the inner code.

The predicates are:
* `QECC.Decodes` — the code recovers perfectly in the absence of errors: `decoder ∘ encoder = id`;
* `QECC.CorrectsErrors k` — any unitary error on at most `k` of the qudits (identity on the rest) is
  perfectly corrected by the decoder;
* `QECC.DetectsErrors k` — there is a flagging decoder that always recovers the logical state
  correctly when it does not raise its flag, for any weight-`≤ k` unitary error.

## Implementation notes

The generality (arbitrary CPTP encoders/decoders, and general finite Hilbert spaces) means the
`i`-indexed physical space `i → d2` requires `[DecidableEq i]` for its `Fintype`/`DecidableEq`
instances, so `QECC` carries that instance in addition to the ones on `d1`, `i`, and `d2`.
-/

open scoped Matrix

namespace QuantumLib

/-! ### Auxiliary lemmas on `CPTPOp.ofEquiv` -/

namespace CPTPOp
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Relabelling by `e` and then by `e.symm` is the identity channel. -/
theorem ofEquiv_symm_comp (e : a ≃ b) :
    CPTPOp.ofEquiv e ∘ₘ CPTPOp.ofEquiv e.symm = CPTPOp.id := by
  apply CPTPOp.funext
  intro ρ
  simp only [CPTPOp.compose_eq, CPTPOp.ofEquiv_apply, Equiv.symm_symm,
    MState.relabel_relabel, Equiv.symm_trans_self, MState.relabel_refl, CPTPOp.id_MState]

/-- Relabelling by `e.symm` and then by `e` is the identity channel. -/
theorem ofEquiv_comp_symm (e : a ≃ b) :
    CPTPOp.ofEquiv e.symm ∘ₘ CPTPOp.ofEquiv e = CPTPOp.id := by
  have := ofEquiv_symm_comp e.symm
  rwa [Equiv.symm_symm] at this


/-- `CPTPOp.piProd` of identity channels is the identity. (Present in later physlib; stubbed at
the v4.28 pin — an ATP target.) -/
theorem piProd_id {ι : Type*} [DecidableEq ι] [Fintype ι] {d : ι → Type*}
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] :
    CPTPOp.piProd (fun i => (CPTPOp.id : CPTPMap (d i) (d i))) = CPTPOp.id := by
  -- Proof found by the ATP MCP (2026-07-13).
  apply CPTPOp.ext
  ext
  simp [CPTPOp.piProd, MatrixMap.piProd, CPTPOp.id]

end CPTPOp

/-- Mixing two points with weight `1` returns the first. (Companion to `Mixable.mix_zero`.) -/
theorem Mixable.mix_one {U T : Type*} [AddCommMonoid U] [Module ℝ U] [inst : Mixable U T]
    (x₁ x₂ : T) : Mixable.mix (1 : Prob) x₁ x₂ = x₁ := by
  apply inst.to_U_inj
  simp [Mixable.mix, Mixable.mix_ab]

/-! ### The `QECC` structure -/

/-- A quantum error-correcting code: an `encoder` mapping the logical space `d1` into an `i`-indexed
register of `d2`-qudits, and a `decoder` mapping back. No properties are required at this stage; the
useful ones (`Decodes`, `CorrectsErrors`, `DetectsErrors`) are predicates defined below. -/
structure QECC (d1 i d2 : Type*)
    [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1] [Fintype d2] [DecidableEq d2] where
  /-- The encoding channel, taking a logical state to the physical register. -/
  encoder : CPTPMap d1 (i → d2)
  /-- The decoding channel, taking the physical register back to a logical state. -/
  decoder : CPTPMap (i → d2) d1

namespace QECC

variable {d1 d2 i j : Type*}
variable [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1] [Fintype d2] [DecidableEq d2]

/-! ### Constructions -/

/-- The trivial (identity) code on `i → d2`, obtained when the logical space *is* the physical
register. Both the encoder and decoder are the identity channel. -/
noncomputable def identity (i d2 : Type*) [Fintype i] [DecidableEq i] [Fintype d2] [DecidableEq d2] :
    QECC (i → d2) i d2 where
  encoder := CPTPOp.id
  decoder := CPTPOp.id

variable {i' d2' : Type*} [Fintype i'] [DecidableEq i'] [Fintype d2'] [DecidableEq d2']

/-- Composition of two codes: the physical register `i → d2` of the first is the logical space of the
second. The result encodes `d1` all the way into `i' → d2'`. -/
noncomputable def comp (C₁ : QECC d1 i d2) (C₂ : QECC (i → d2) i' d2') : QECC d1 i' d2' where
  encoder := C₂.encoder ∘ₘ C₁.encoder
  decoder := C₁.decoder ∘ₘ C₂.decoder

variable [Fintype j] [DecidableEq j]

/-- The parallel construction: `j` independent copies of a code, run side by side. A `QECC d1 i d2`
lifts to a `QECC (j → d1) (j × i) d2`, where the `j × i` physical qudits are the `j` blocks of `i`
qudits. Built from the Pi-Kronecker product of the per-copy channels, reindexed by currying. -/
noncomputable def parallel (C : QECC d1 i d2) : QECC (j → d1) (j × i) d2 where
  encoder :=
    CPTPOp.ofEquiv (Equiv.curry j i d2).symm ∘ₘ CPTPOp.piProd (fun _ : j => C.encoder)
  decoder :=
    CPTPOp.piProd (fun _ : j => C.decoder) ∘ₘ CPTPOp.ofEquiv (Equiv.curry j i d2)

variable {d1' : Type*} [Fintype d1'] [DecidableEq d1']

/-- Concatenation of codes: each physical qudit of the `outer` code is itself the logical space of
the `inner` code (so `d1` of the inner equals `d2` of the outer). The concatenated code encodes `d1`
into `(io × ii) → d2`. This is the outer code composed with the `io`-fold parallel construction of
the inner code. -/
noncomputable def concat {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]
    (outer : QECC d1 io d1') (inner : QECC d1' ii d2) : QECC d1 (io × ii) d2 :=
  comp outer (parallel (j := io) inner)

/-! ### The `Decodes` predicate -/

/-- A code `Decodes` if, in the absence of any error, the decoder perfectly inverts the encoder. -/
def Decodes (C : QECC d1 i d2) : Prop :=
  C.decoder ∘ₘ C.encoder = CPTPOp.id

@[simp]
theorem identity_decodes : (identity i d2).Decodes := by
  simp [Decodes, identity]

/-- Decoding is preserved under composition of codes. -/
theorem comp_decodes {C₁ : QECC d1 i d2} {C₂ : QECC (i → d2) i' d2'}
    (h₁ : C₁.Decodes) (h₂ : C₂.Decodes) : (C₁.comp C₂).Decodes := by
  simp only [Decodes, comp] at *
  rw [CPTPOp.compose_assoc, ← CPTPOp.compose_assoc C₂.decoder, h₂, CPTPOp.id_compose, h₁]

/-- Decoding is preserved under the parallel construction. -/
theorem parallel_decodes {C : QECC d1 i d2} (h : C.Decodes) :
    (parallel (j := j) C).Decodes := by
  simp only [Decodes, parallel] at *
  rw [CPTPOp.compose_assoc, ← CPTPOp.compose_assoc (CPTPOp.ofEquiv (Equiv.curry j i d2)),
    CPTPOp.ofEquiv_symm_comp, CPTPOp.id_compose, ← CPTPOp.piProd_comp]
  simp only [h, CPTPOp.piProd_id]

/-- Decoding is preserved under concatenation of codes. -/
theorem concat_decodes {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]
    {outer : QECC d1 io d1'} {inner : QECC d1' ii d2}
    (h₁ : outer.Decodes) (h₂ : inner.Decodes) : (outer.concat inner).Decodes :=
  comp_decodes h₁ (parallel_decodes h₂)

/-! ### A dimension (cardinality) bound -/

/-- If a code decodes, its logical dimension cannot exceed the physical dimension: a code that
faithfully recovers `d1` needs `card d1 ≤ card d2 ^ card i`. This is the basic counting bound behind
statements like the quantum Singleton bound. -/
theorem card_le_of_decodes {C : QECC d1 i d2} (h : C.Decodes) :
    Fintype.card d1 ≤ Fintype.card d2 ^ Fintype.card i := by
  have h' : C.decoder ∘ₘ C.encoder = CPTPOp.id := h
  have hmap : C.decoder.map ∘ₗ C.encoder.map = LinearMap.id := by
    show (C.decoder ∘ₘ C.encoder).map = LinearMap.id
    rw [h']; exact CPTPOp.id_map
  have hinj : Function.Injective C.encoder.map :=
    Function.LeftInverse.injective (g := C.decoder.map) (fun x => by
      rw [← LinearMap.comp_apply, hmap, LinearMap.id_apply])
  have hfr := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_matrix, Module.finrank_matrix, Module.finrank_self, mul_one, mul_one] at hfr
  have hcard : Fintype.card d1 ≤ Fintype.card (i → d2) := by
    by_contra hc
    rw [not_le] at hc
    nlinarith [hfr, hc]
  rwa [Fintype.card_fun] at hcard

/-! ### Error channels -/

/-- A unitary error: it acts by the arbitrary unitary `U q` on each qudit `q ∈ S`, and as the
identity on every qudit outside `S`. -/
noncomputable def unitaryError (S : Finset i) (U : i → 𝐔[d2]) : CPTPMap (i → d2) (i → d2) :=
  CPTPOp.piProd (fun q => if q ∈ S then CPTPOp.ofUnitary (U q) else CPTPOp.id)

/-- An error affecting no qudits is the identity channel. -/
@[simp]
theorem unitaryError_empty (U : i → 𝐔[d2]) :
    unitaryError (∅ : Finset i) U = CPTPOp.id := by
  simp only [unitaryError, Finset.notMem_empty, if_false]
  exact CPTPOp.piProd_id

/-! ### Error correction -/

/-- A code `CorrectsErrors k` if a single decoder recovers the logical state exactly after *any*
unitary error acting on at most `k` of the physical qudits (and the identity on the rest). -/
def CorrectsErrors (C : QECC d1 i d2) (k : ℕ) : Prop :=
  ∀ S : Finset i, S.card ≤ k → ∀ U : i → 𝐔[d2],
    C.decoder ∘ₘ unitaryError S U ∘ₘ C.encoder = CPTPOp.id

/-- Correcting `k` errors is stronger than correcting fewer. -/
theorem CorrectsErrors.mono {C : QECC d1 i d2} {k k' : ℕ}
    (h : C.CorrectsErrors k) (hk : k' ≤ k) : C.CorrectsErrors k' :=
  fun S hS U => h S (hS.trans hk) U

/-- Correcting zero errors is exactly decoding correctly in the noiseless case. -/
theorem correctsErrors_zero_iff {C : QECC d1 i d2} : C.CorrectsErrors 0 ↔ C.Decodes := by
  constructor
  · intro h
    have he := h ∅ (by simp) (fun _ => 1)
    rw [unitaryError_empty, CPTPOp.compose_id] at he
    exact he
  · intro h S hS U
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst hS0
    rw [unitaryError_empty, CPTPOp.compose_id]
    exact h

/-- A code that corrects any errors, in particular, decodes correctly. -/
theorem CorrectsErrors.decodes {C : QECC d1 i d2} {k : ℕ} (h : C.CorrectsErrors k) : C.Decodes :=
  correctsErrors_zero_iff.mp (h.mono (Nat.zero_le k))

/-- The identity code corrects zero errors (i.e. it decodes, but does not protect against noise). -/
theorem identity_correctsErrors_zero : (identity i d2).CorrectsErrors 0 :=
  correctsErrors_zero_iff.mpr identity_decodes

/-! ### Error detection

Detection is modelled with a *flagging decoder* `R : CPTPMap (i → d2) (d1 × Fin 2)` whose second
factor `Fin 2` is a flag. The map `prep0` embeds a logical state `ρ ↦ ρ ⊗ |0⟩⟨0|` (accept, flag `0`),
and `flagChannel` is a fixed "rejected" output carrying flag `1`. A code detects errors if, for every
error, the flagging decoder produces a convex mixture of the *perfectly preserved* logical state
(flag `0`) and the flag (flag `1`); in particular, whenever the flag is `0` the logical content is
untouched. -/

/-- The channel `ρ ↦ ρ ⊗ |0⟩⟨0|`, preparing a fresh flag qubit in state `|0⟩`. -/
noncomputable def prep0 (d1 : Type*) [Fintype d1] [DecidableEq d1] :
    CPTPMap d1 (d1 × Fin 2) :=
  (CPTPOp.id ⊗ᶜᵖ CPTPOp.replacement (dIn := Unit) (MState.pure (Ket.basis (0 : Fin 2)))) ∘ₘ
    CPTPOp.ofEquiv ((Equiv.prodPUnit d1).symm : d1 ≃ d1 × Unit)

/-- A fixed "error detected" output state, carrying flag `1`. -/
noncomputable def flagChannel (d1 : Type*) [Fintype d1] [DecidableEq d1] [Nonempty d1] :
    CPTPMap d1 (d1 × Fin 2) :=
  CPTPOp.replacement
    (MState.pure (Ket.basis (Classical.choice (α := d1) inferInstance, (1 : Fin 2))))

/-- A code `DetectsErrors k` if there is a flagging decoder that, for every unitary error of weight
`≤ k`, returns a convex mixture of the perfectly-preserved logical state (with flag `0`) and the
flag (flag `1`). When no error occurs (`R ∘ₘ encoder = prep0`) it always accepts with the correct
state. -/
def DetectsErrors (C : QECC d1 i d2) [Nonempty d1] (k : ℕ) : Prop :=
  ∃ R : CPTPMap (i → d2) (d1 × Fin 2),
    R ∘ₘ C.encoder = prep0 d1 ∧
    ∀ S : Finset i, S.card ≤ k → ∀ U : i → 𝐔[d2],
      ∃ p : Prob, R ∘ₘ unitaryError S U ∘ₘ C.encoder = Mixable.mix p (prep0 d1) (flagChannel d1)

/-- Detecting `k` errors is stronger than detecting fewer. -/
theorem DetectsErrors.mono {C : QECC d1 i d2} [Nonempty d1] {k k' : ℕ}
    (h : C.DetectsErrors k) (hk : k' ≤ k) : C.DetectsErrors k' := by
  obtain ⟨R, hR0, hRS⟩ := h
  exact ⟨R, hR0, fun S hS U => hRS S (hS.trans hk) U⟩

/-- Any code that corrects `k` errors also detects them: use the (never-flagging) decoder that
prepares flag `0` after decoding. -/
theorem CorrectsErrors.detectsErrors {C : QECC d1 i d2} [Nonempty d1] {k : ℕ}
    (h : C.CorrectsErrors k) : C.DetectsErrors k := by
  have hd : C.decoder ∘ₘ C.encoder = CPTPOp.id := h.decodes
  refine ⟨prep0 d1 ∘ₘ C.decoder, ?_, ?_⟩
  · rw [CPTPOp.compose_assoc, hd, CPTPOp.compose_id]
  · intro S hS U
    refine ⟨1, ?_⟩
    have herr : (C.decoder ∘ₘ unitaryError S U) ∘ₘ C.encoder = CPTPOp.id := h S hS U
    rw [Mixable.mix_one, CPTPOp.compose_assoc, CPTPOp.compose_assoc,
      ← CPTPOp.compose_assoc C.decoder, herr, CPTPOp.compose_id]

end QECC

end QuantumLib
