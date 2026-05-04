/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

/-!
# Defining Quantum Capacity

Quantum capacity is defined in different reference works in at least seven meaningfully different ways:

(1) https://www.uio.no/studier/emner/matnat/math/MAT4430/v23/timeplan/lectureblup.pdf, Defn 20.3.

Defines the notion of "(n, m, δ)-coding scheme", a code for m qubits in n copies of the channel, with diamond-norm distance of δ from the identity channel. Then a rate R is "achievable" if there is a sequence of coding schemes that converge m/n -> R and δ -> 0. The set of achieveable rates is a closed interval, and the capacity is the maximum of this interval.

(2) https://cs.uwaterloo.ca/~watrous/TQI/TQI.8.pdf, Defn 8.42.

Watrous doesn't use the word "coding scheme", but rather define "emulating" (8.1) an "ε-approximation" (8.2) of the identity. This is equivalent to the coding scheme and diamond norm part. Then a rate R is "achievable" if, for every δ>0, there is a k:ℕ such that k < n implies the existence of a (n, floor(R*n), δ)-coding scheme. Now the set of achievable rates may be an open or closed interval, and the capacity is the supremum of this interval (not the maximum, since an open interval has no maximum).

(3) Works like https://arxiv.org/pdf/1007.2855 (equation 3) and https://arxiv.org/pdf/1801.02019 (equation 186) define the quantum capacity of C as $Q(C) = lim_n 1/n * Q^{(1)}(C ^ {⊗n})$, where $Q^{(1)}$ is the quantum coherent information (or "one-shot channel capacity"), and so it is the average coherent information achieved across n copies of the channel, in the large-n limit. This definition makes the LSD theorem (which stats that $Q ≥ Q^{(1)}$) actually entirely trivial, as it requires only the fact that $Q^{(1)}$ is superadditive.

(4) https://arxiv.org/pdf/quant-ph/0304127 (Section 5) and https://arxiv.org/pdf/quant-ph/9809010 specifically distinguish between "subspace transmission", "entanglement transmission", and "entanglement generation" capabilities of the channel. The fact that all three are equal is then a theorem. Option (4), subspace transsmission capacity, is like option (1) above, but instead of the channel having diamond norm at most δ from the identity channel, we require that the channel has fidelity at least 1-δ on all inputs. Converging in fidelity is surely equivalent to converging in diamond norm, but the precise bounds are not obvious. (4) also differs from (1) and (2) in that it has an arbitrary dimension input space, instead of specifically a 2^n-dimensional space of qubits. arxiv:9809010 specifically requires a sequence of codes whose limiting fidelity is 1 and rate is R; arxiv:0304127 doesn't actually precisely say.

(5) "Entanglement transmission" asks for a high-entropy state (thus, a large subspace dimension) that can be transmitted through the channel with a high "entanglement fidelity". See equation (52) in arxiv:0304127. The rate achieved is the von Neumann entropy of the state, the set of achievable rates are closed, and the rate of the channel is the maximum.

(6) "Entanglement generation" changes the task from coding. Instead we need a bipartite state ρ_AB on a Hilbert space of dimension κ, of which the left half goes through the encoder, channel, and decoder. The fidelity between the result C(ρ) and the maximally entangled state must be at least 1-ε. The rates are (1/n)*(log κ), achievable if for all δ and sufficiently large n (etc. - like option (2)), and we take the supremum.

Note: Option (6) is what Devetak, in arxiv:0304127, actually proves the LSD theorem for. Theorem 5 in that reference. (4), (5), and (6) are proven equal.

(7) Wilde's book also of "coding scheme", but defines it in terms of entanglement generation and the logarithm of the dimension of the space. Instead of fidelity preserved in the entanglement, it's the trace norm. He effectively defines it by supremum, although he doesn't need to use the word, giving an equivalent δ/ε definition for coding schemes. He then takes supremum (even though maximum would work as well -- the capacity is itself an achievable rate by his definition). In this way, it combines aspects of definitions (1), (2), and (4). He gives as an exercise showing that small trace norm error of transmitted states implies a small diamond norm error from the identity.

----

To capture the idea of "quantum capacity", and some other idea that turns out to be equivalent, (1), (2), or (5) seems best. The definitions (1) and (2) seem to be the more recently popular ones. Between those two, choosing "supremum" or "maximum", the supremum seems shorter to state in a definition (as it doesn't require proving closure); indeed Mathlib has no notion of "max real" as a function, only a supremum which can also be shown to be in the set. But the definition in (2) of "For every δ>0, there is a k:ℕ such that k < n implies the existence of a (...)-coding scheme" is cleaner work with as a way to directly construct or extract codes, as opposed to limits of sequences of codes. And finally, the notions of "emulate" and "approximate" seem useful for defining it more elegantly.

This leads to the final definition in [Capacity.lean](./QuantumInfo/Finite/Capacity.html).
-/@[expose] public section
