# QuantumInfo linter-exemption cleanup — notes for maintainers

A community pass removed **59 of 84** `QuantumInfo/` files from `scripts/LinterExemption.txt`
(each now passes `lake exe runPhyslibLinters` + `scripts/lint-style.py`, verified by a full
`QuantumInfo` build, Lean v4.30.0). The **25 files left exempted** could not be cleared by
docstring/style work alone; they are grouped below with a suggested path forward so the effort
isn't silently blocked.

(One disclosed mechanical choice in the de-exempted set: `Channels/Bundled.lean` uses
`attribute [nolint docBlame]` on 4 auto-generated multi-parent projections — `PTPMap.toTPMap`,
`PUMap.toUnitalMap`, `CPTPMap.toCPMap`, `CPUMap.toPUMap` — which cannot take doc-strings without
breaking field-projection inference. Standard Batteries mechanism; flagging it for visibility.)

## A. Exceed the 1500-line cap (`ERR_NUM_LIN`) — need a file SPLIT (6)

`lint-style.py` fails any file >1500 lines without a watermark in `scripts/style-exceptions.txt`
(currently empty). Wrapping long lines only *adds* lines, so these can't be cleared by wrapping.

| File | lines | ~lines after wrapping |
|------|------:|----------------------:|
| `Entropy/Relative.lean` | 2455 | ~2825 |
| `ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean` | 2406 | ~2436 |
| `ResourceTheory/SteinsLemma.lean` | 2122 | ~2272 |
| `ForMathlib/Matrix.lean` | 1600 | ~1752 |
| `ForMathlib/HermitianMat/CFC.lean` | 1446 | ~1660 |
| `States/Mixed/MState.lean` | 1398 | ~1503 |

**Suggested:** split each into logical sub-modules (keeps every file <1500), **or** add a
watermark entry to `scripts/style-exceptions.txt` (the linter's own mechanism for legitimately
large files) to de-exempt now and split later.

## B. Do not build on the clean baseline (HEAD) — need a compile fix (2)

These fail `lake build` *before any cleanup*, so they cannot be verified/de-exempted until fixed.

- **`Entropy/Axiomatized/Defs.lean`** — `Defs.lean:68:53 expected token`; `69:95 unexpected
  identifier; expected 'lemma'`; `110 Unknown constant CPTPMap.of_equiv`. Looks like a rename
  (`CPTPMap.of_equiv` gone) plus a syntax error.
- **`ResourceTheory/ResourceTheory.lean`** — `48 failed to synthesize instance`; `48 Unknown
  identifier prod`. The `IsTensorial` def references an unknown `prod` / fails type-class
  synthesis — likely API drift in the tensor structure.

**Suggested:** fix the (apparently rename-induced) compile errors, then lint normally.

## C. `unusedArguments` with *multiple* unused instance args (8)

These have unused instance binders the linter flags; removing one exposes another (the linter
reports them one at a time), so a real fix is iterative signature surgery with downstream-rebuild
risk — best done by someone who knows the intended API.

- `Channels/CPTP.lean` (`CPTPMap.replacement`, `[Nonempty]`)
- `Channels/Unbundled.lean` (`MatrixMap.IsPositive`, multiple `[Fintype]`)
- `ClassicalInfo/Distribution.lean` (`map_congr_eq_congr_map`, `[Mixable]`; also def→theorem)
- `Entropy/VonNeumann.lean` (`vecToMat`, multiple `[Fintype]`)
- `ForMathlib/ComplexLaplaceTransform.lean` (`[MeasurableSpace]` ×2)
- `ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean` (`HSum`, `[InnerProductSpace]`)
- `ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean` (`HSIndex`, `[FiniteDimensional]`)
- `ForMathlib/Majorization.lean` (`fintypeLinearOrderClassical`, `[Fintype]`)

**Suggested:** decide per declaration whether each flagged instance is truly removable; remove all
unused ones in one pass and rebuild dependents. (We did not, to avoid breaking call sites.)

## D. Contain pre-existing `sorry` — not proof-complete (5)

These pass the doc/style linters but still contain `sorry`, so we deliberately left them exempted
rather than imply they're finished. The doc/style fixes were reverted with them.

- `Entropy/Axiomatized/Renyi.lean` — `qRelativeEnt` nonneg (needs **Klein's inequality**);
  `RelEntropy` instance `DPI` / `of_kron` / `normalized` and `Nontrivial.nontrivial` all `sorry`.
  (`DPI` = data-processing inequality for quantum relative entropy — a major QIT theorem.)
- `Capacity/Capacity.lean` (3 sorries), `ClassicalInfo/Capacity.lean` (4 stub fields),
  `States/Mixed/Fidelity.lean` (1), `ForMathlib/Misc.lean` (`subtype_val_iSup'`, an order-theory
  `iSup`-on-subtype lemma — the most tractable of the set).

**Suggested:** these are genuine proof obligations for the authors. `Misc.subtype_val_iSup'` is
plausibly a quick order-theory fill; the relative-entropy/capacity ones are research-level.

## E. Tractable but not finished in this pass (4)

No blocker — just incomplete when the pass stopped. Each needs docstrings/line-wraps (and a noted
safe code-level fix). A follow-up can clear them.

- `ForMathlib/HermitianMat/Inner.lean` (27 style left; `RCLike.instOrderClosed` def→theorem)
- `ResourceTheory/FreeState.lean` (`spacePow_zero`/`spacePow_one` drop `@[simp]` + docstrings)
- `States/Pure/Qubit.lean` (drop `@[simp]` from `controllize_mul_inv` + docstrings)
- `States/Pure/Braket.lean` (`normalize_ket_eq_self` def→theorem + many line-wraps + docstrings)

---
*Community linter-exemption cleanup, Lean v4.30.0. The 59 de-exempted files were each verified
sorry-free and axiom-free (no `sorry`/`axiom`/`admit`/`set_option … false` added).*
