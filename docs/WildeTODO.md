# Matching QuantumInfo to _Quantum Information Theory_

Mark Wilde's book "Quantum Information Theory" provides a solid guide to QIT in general; early on
in the development of `QuantumInfo`, it was conceived that we could try to match the repository to
that book where reasonably possible as a way to ensure good coverage. This document generally
gives that correspondence, although it may be rather out of date (probably last current as of
early 2025). Of course there's also a lot of content in `QuantumInfo` that goes well beyond the scope
of that book, too.

Each of the items below is an item in Mark Wilde's book, "Quantum Information Theory". The following emoji indicate possible status:
 * ✅ - Completed, and proved with no `sorry`s.
 * 📝 - All required definitions are present and the question is stated / the theorem is in a form that could be used, but it is unproved / depends on `sorry`.
 * ❓ - This has not yet been stated or fully defined.
 * 🤷 - This is unlikely / undesirable to be formalized.
 * 😂 - This didn't need to be proved, because it was just the definition (or something similar).
 * 🤔 - This is not a fact in the book but something related that would be nice to have (and we don't have yet).

There's very little from Chapters 2 or 3 to include right now. Chapter 2 is an intuitive (and less rigorous) overview of classical coding theory. Chapter 3 is a lot of practice of qubit computations, and we haven't worked the special case of qubits yet much.

# Chapter 2 - Classical Shannon Theory
Exercise 2.1.1: The entropy of a uniform variable is `log |X|`, where `|X|` is the size of the variable's alphabet.
 ✅ `Hₛ_uniform` in `ClassicalInfo.Entropy`.

Property 2.1.1, 2.1.2, 2.1.3: Basic properties of typical sets.
🤷 Typical sets aren't defined until Chapter 14, we will prove things then.

Exercise 2.2.1: If the average (across codewords) probability of a codeword C getting incorrectly decoded is ε, then by Markov's inequality least half of the codewords have at most 2ε of incorrect decoding.
🤷 `ENNReal.finset_card_const_le_le_of_tsum_le` states the interesting bit (Markov's inequality for finite set cardinalities), the application to codewords will come when we need it.

# Chapter 3 - The Noiseless Quantum Theory
Bras, Kets
✅ `Bra` and `Ket` in `QuantumInfo.States.Pure.Braket`.

Exercise 3.2.1: Determine the Bloch sphere angles for the states ∣-〉and ∣+〉.
❓ Eventually we'll define qubits, basic states like these, and the Bloch sphere, and can add lemmas for these.

Exercise 3.3.1: A linear operator unitary iff it is norm-preserving.
❓ This is stated for linear operators as `unitary.linearIsometryEquiv`, and the "only if" is more explicitly as `unitary.norm_map`. Would be good to have for `Matrix.unitaryGroup`.

_There's a whole bunch about Pauli matrices. We haven't specialized to qubits yet, so these are all ❓._

Exercise 3.3.2: Find a matrix representation of `[X,Z]` in the basis ∣0〉, ∣1〉.
Exercise 3.3.3: Show that the Pauli matrices are all Hermitian, unitary, and square to the identity, and their eigenvalues are ±1.
Exercise 3.3.4: Represent the eigenstates of the Y operator in the standard computational basis.
Exercise 3.3.5: Show that the Paulis either commute or anticommute.
Exercise 3.3.6: With σi, i=0..3, show that Tr{σi σj} = δij.
Exercise 3.3.7: Matrix representation of Hadamard gate.
Exercise 3.3.8: Hadamard is its own inverse.
Exercise 3.3.9: A particular exercise in changing bases; this is 🤷.
Exercise 3.3.10: HXH = Z and HZH=X. _Sure, if we make simp lemmas for Clifford products this can be in there._

Definition 3.3.1: Function of a Hermitian operator (by a function on its spectrum).
❓ This we definitely would like, currently they're all ad-hoc.

Exercise 3.3.11: Explicit forms for rotation operators.
❓ Requires Bloch sphere and rotation gates. Will probably be the definitions of them.

Postulate: Born rule.
✅ We have `MState.measure` which has this baked in. But we could also have it for bras and kets.

Definition: von Neumann measurement. A POVM that is not just projective, but given by an orthonormal basis.
❓ Could be a nice Prop on POVMs.

Exercise 3.4.1: POVM associated to the X operator measurement.
❓ Definitely want this.

Exercise 3.4.2, 3.4.3: Asking (something like) `〈ψ∣H∣ψ〉= Ex[H.measure (pure ψ)]`.
❓ Definitely want to prove. Doesn't need qubits, either.

Uncertainty principle
❓ Could do the state-dependent version given in the book. The averaged-case expectation value one comes as a result. But this would require defining + working with the Haar measure over kets.

Exercise 3.4.4, 3.4.5: Longish story about uncertainty princple.
🤷 Won't prove the thing asked, it's a very specific thing.

Exercise 3.5.1: This is askings for products of operators on qubits as tensor products.
😂 This is precisely how we define it to start with.

Exercise 3.5.2: Asking that`〈ξ1⊗ξ2‖ψ1⊗ψ2〉=〈ξ1‖ψ1〉〈ξ2‖ψ2〉`.
❓ Basic fact about braket products types.

Exercise 3.5.3: Matrix representation of CNOT gate as [1,0,0,0;0,1...] etc.
✅ In `Qubits.Basic`, defined using `Qubit.controllize` and proven equivalent to the above matrix

Exercise 3.5.4: Prove `(H⊗H)(CNOT)(H⊗H) = |+⟩⟨+|⊗I + |-⟩⟨-|⊗Z`.
🤷 Very specific equality.

Exercise 3.5.5: `CNOT(1→2)` commutes with `CNOT(1→3)`.
Exercise 3.5.6: `CNOT(2→1)` commutes with `CNOT(3→1)`.
❓ Depending on how we define the qubits to a gate, might be fine (in which case let's do the generic one for any controlled gate), or a pain.

No-Cloning theorem (for unitaries): There is no unitary that clones perfectly from |ψ0⟩ to |ψ0⟩.
❓ Should be easy to state and prove.
🤔 No-Cloning theorem (for channels): There is no channel that clones perfectly from ρ to ρ⊗ρ.
🤔 Proving the bounds on the optimal universal quantum clone (5/6 fidelity etc.)

Exercise 3.5.7: Orthogonal states can be perfectly cloned.
❓ Stated for two orthogonal qubit states, we'll prove for orthogonal sets of qudits.

Exercise 3.5.8: No-Deletion theorem. No unitary from |ψψA⟩ to |ψ0B⟩ for fixed ancilla states A and B.
❓

Definition 3.6.1: Entangled pure states.
✅ `Ket.IsEntangled` in `QuantumInfo.States.Pure.Braket`

Exercise 3.6.1, 3.6.2: The Bell state = `( |++⟩ + |--⟩ )/√2`. This means shared randomness in Z or X basis.
🤷 Too specific. _Could_ say something like "the Bell state is identical in many bases", which is Exercise 3.7.12.

Exercise 3.6.3: Cloning implies signalling.
🤷 If we can prove that cloning doesn't exist, this gives an immediate exfalso proof, so this isn't interesting.

CHSH Game
❓ Defining it, giving optimal classical and quantum strategies.

Exercise 3.6.5, 3.66, 3.6.7: Numerical exercises with Bell states.
🤷 Maybe just defining Bell states as a basis for 2-qubit states.

Exercise 3.7.1 - 3.7.11: Lemmas about qudit X and Z operators.
❓ Sure, if we define them.

Exercise 3.7.12: "Transpose trick" for Bell state |Φ⟩, that `(U⊗I)|Φ⟩=(I⊗Uᵀ)|Φ⟩`.
✅ `transposeTrick` in `Braket.lean`.

Theorem 3.8.1, Exercise 3.8.1: Schmidt Decomposition.
❓

Exercise 3.8.2: Schmidt decomposition determines if a state is entangled or product.
❓

# Chapter 4 - The Noisy Quantum Theory
Definition 4.1.1: Matrix trace.
✅ `Matrix.trace` in Mathlib.

Exercise 4.1.1: The trace is cyclic.
✅ `Matrix.trace_mul_cycle` in Mathlib.

Definition 4.1.2: Defining the density operator of an ensemble.
❓ We define density operators, but could write an "of_ensemble" function.

Exercise 4.1.2: The density matrix of `pure (indicator 0)`.
🤷 Feels specific and not like a useful lemma.

Exercise 4.1.3: Matrix trace as the expectation value of maximally entangled state.
❓

Exercise 4.1.4: Trace of operator functions, `Tr[f(GG*)] = Tr[f(G*G)]`.
❓ Requires Definition 3.3.1 first.

Exercise 4.1.5: Computing density operators of some particular ensembles.
🤷

Exercise 4.1.6: The spectrum of a density operator forms a distribution.
✅ `MState.spectrum` is a `Distribution`, in `QuantumInfo.States.Mixed.MState`.

Definition 4.1.3: The density operator is a PSD operator with trace 1.
✅ `MState` in `QuantumInfo.States.Mixed.MState`.

Definition 4.1.4: The maximally mixed state.
✅ `MState.uniform` in `QuantumInfo.States.Mixed.MState`.

Exercise 4.1.7: A uniform ensemble of {|0⟩, |1⟩, |+⟩, |-⟩} is the maximally mixed state.
🤷

Exercise 4.1.8: The set of density operators is a convex set.
✅ `MState.instMixable` in `QuantumInfo.States.Mixed.MState`.

Definition 4.1.5: Purity of a mixed state.
✅ `MState.purity` in `QuantumInfo.States.Mixed.MState`.

Exercise 4.1.9: Purity is equal to 1 iff the state is pure.
✅ `MState.pure_iff_purity_one` in `QuantumInfo.States.Mixed.MState`.

Exercise 4.1.10-4.1.13: Specific to qubits and the Bloch sphere.
❓

Unitary Evolution of a Mixed State
✅ `MState.U_conj` in `QuantumInfo.Finite.Unitary`

Evolution of an ensemble of mixed states
❓ Could define ensemble as distribution over a finite set of MStates.

Exercise 4.1.14, 4.1.15: Some facts about embedding classical probabilities into quantum states.
🤷 Probably not useful for anything else.

Definition 4.2.1: POVMs as PSD matrices that sum to the identity.
✅ `POVM` in `QuantumInfo.Measurements.POVM`.

Exercise 4.2.1: The five "Chrysler" states on a qubit, scaled down by (2/5), form a POVM.
🤷 Very specific.

Exercise 4.2.2(a): Suppose an ensemble ρ_X has a bound τ, so that ∀(x ∈ X), τ ≽ p_x ρ(x). Then the maximum expected probability of a POVM identifying x from the distribution is at most Tr[τ].
Exercise 4.2.2(b): In a d dimensional ensemble, no more than d possible symbols can be lossessly stored.
❓ Seems unlikely to be used later but fine to state and prove.

Definition 4.3.1: Product State (density operator).
✅ `MState.prod` in `QuantumInfo.States.Mixed.MState` constructs product states. No predicate form.

Exercise 4.3.1(a): `ρ.purity = (U_swap * ρ ⊗ ρ).trace`.
Exercise 4.3.1(b): For an operator function `f`, `Tr[f(ρ)] = ( f(ρ) ⊗ I(d) ).swap.trace`.
❓ Should be an easy index chase.

Exercise 4.3.2: Just a step of a scenario, not really a theorem.
🤷

Exercise 4.3.3: Every separable state `Σ x, ρx ⊗ σx` is also of the form `∑ x, pure (φ x) ⊗ pure (ψ x)`.

Definition 4.3.2: Separable state.
✅ `MState.IsSeparable` in `QuantumInfo.States.Mixed.MState`.

Definition 4.3.3: Entangled (mixed) state.
✅ `MState.IsEntangled` in `QuantumInfo.States.Mixed.MState`.

Exercise 4.3.4: Convexity of separable states.
❓ Will have to write this as `Mixable { ρ : MState (d₁ × d₂) // ρ.IsSeparable }`.
