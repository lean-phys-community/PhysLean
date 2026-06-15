# AGENTS.md

Instructions for AI agents contributing to Physlib. The human-facing policy and disclosure
obligations are in [AI-POLICY.md](AI-POLICY.md); read it too. You produce the code, but the human
author certifies it: a clean build proves you proved what was written, never that it is what they
meant.

Also obey [docs/ReviewGuidelines.md](docs/ReviewGuidelines.md) and the Mathlib [style
guide](https://leanprover-community.github.io/contribute/style.html).

## Content

- Use `lemma`, not `theorem`, unless the result is well known in the physics literature.
- No `axiom` declarations. No `sorry` in submitted work.
- Do not add lemmas that are trivial rewrites of existing Mathlib or Physlib results, unless they
  add genuine physics context.
- Place results in the appropriate existing file; do not create new files without good reason.
- Number sections `# A. ...`, `## A.1. ...`. See
  [HarmonicOscillator/Basic.lean](Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean).
- All content must pass the linters in [scripts/README.md](scripts/README.md).

## Proof structuring

These are reviewer-judgment questions, not mechanical rules. **Surface a recommendation** when a
condition below is met and let a human make the structural call; do **not** split or relocate lemmas
unilaterally.

A proof can mix concerns three ways. Flag whichever discriminator fires:

| Type | Discriminator | Extracted lemma's statement |
|---|---|---|
| **Depth** | Contiguous block cites only general lemmas (`Finset.*`, `ring`, Mathlib), untouched by physics constants | Contains **zero** physics names |
| **Breadth** | Proof cites lemmas from **two disjoint physics topic namespaces** | Each piece sits in **one** namespace |
| **Computation** | Large contiguous `calc`/`ring_nf`/`field_simp`/`positivity` slab under a structural top-level tactic | A calculation lemma (may keep physics constants) |
| **Leave inline** | Not a contiguous subgoal-closing block, or one indivisible argument | — |

Rule: if the candidate cannot be cut as a contiguous run that closes its own subgoal, do not
recommend splitting it.

**Depth-mixing example.** The general-algebra block below is statable with no physics vocabulary, so
it should become its own lemma:

The Lean below is illustrative pseudocode (invented `ParticleSystem` API), not a compiling snippet;
it shows the *shape* of the refactor, not exact lemma names.

```lean
-- Before: general Finset plumbing inlined under a physics statement
theorem totalKE_eq_sum (s : ParticleSystem n) :
    s.totalKE = ∑ i, s.kineticEnergy i := by
  unfold ParticleSystem.totalKE ParticleSystem.kineticEnergy
  rw [Finset.mul_sum]   -- ← cites only Finset/ring, no physics constants
  congr 1; ext i; ring

-- After: the plumbing is named; its statement has zero physics names
private lemma half_mul_sum {n : ℕ} (f : Fin n → ℝ) :
    (1 / 2) * ∑ i, f i = ∑ i, (1 / 2) * f i := by
  rw [Finset.mul_sum]

theorem totalKE_eq_sum (s : ParticleSystem n) :
    s.totalKE = ∑ i, s.kineticEnergy i := by
  unfold ParticleSystem.totalKE ParticleSystem.kineticEnergy
  rw [half_mul_sum]
  congr 1; ext i; ring
```

Length alone is not a reason to split: a long proof that is one indivisible argument should stay
whole — especially foundational results, where added inter-lemma structure can be more fragile than
the length costs in readability.

## PR scope

A PR should add a **single coherent concept**. Cohesion governs, **not** line count.

- Every definition and lemma should either *be* that concept or supply the minimal API to state and
  prove it.
- Match the surrounding house pattern (e.g. one concept per file, developed with its full API).
- A long but well-sectioned file (module docstring with overview, key results, table of contents) is
  reviewable whole; do not fragment one concept across PRs to hit a line count.
- Line count is a smell, not a gate: the [Review Guidelines](docs/ReviewGuidelines.md) thresholds
  prompt the cohesion questions above. Split only along conceptual seams. Refactors,
  reorganizations, and docs PRs may safely run larger. Surface an oversized-PR concern for a human;
  do not split to satisfy a number.

## Commits

- Split a PR into atomic commits where it makes sense; keep commits focused.
- Commit titles must describe the lemmas or definitions added or changed.
- Include a [sign-off](https://git-scm.com/docs/SubmittingPatches.html#sign-off)-style
  `Co-authored-by: Claude Opus 4.8 <no-reply+claude-opus-4-8@anthropic.com>` trailer on commits you
  produced.
