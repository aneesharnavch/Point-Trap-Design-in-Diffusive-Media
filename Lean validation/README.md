# Time Traps: complete Lean source release

Aneesh Arnav Chikkala · 15 September 2026

This package contains the exact sealed research sources used by the four-paper
publication: 2,282 research modules, 10,543 named theorems, `TimeTraps.lean`, and
`Audit.lean`. It contains no `.lake` build products, dependency binaries, or
machine-specific import tables.

## What was verified

The historical final certificate is preserved byte-for-byte in
`evidence/three-paper-closure-verification.json`. Its SHA-256 is
`1fcbfe88f6dde12cc7342af18d97c843e5f6e00e81f9657abe7b355312f649ee`.
It records frozen baseline checks plus exact checks of every new module and
fresh integrated root/transitive-axiom checks. Its 17,355 audited declarations
include generated helpers as well as the 10,543 named theorems. These counts
are not numbers of independent mathematical discoveries.

The allowed foundational axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`. The source guard is supplementary; the transitive Lean audit
is the authoritative dependency check. Classical/noncomputable definitions do
not claim an executable floating-point implementation.

A new clean build of this extracted release has **not** been performed for
this publication. The source/hash/inventory checks and the deterministic
numerical driver have been run. Historical records are never relabeled as a
fresh clean build. The original certificate's explicit scope qualifications
are reproduced in `evidence/closure-summary.json`.

## Files and mapping

- `lean/`: complete source project, exact pinned toolchain, Lake configuration
  and manifest, plus the original proof-source guard.
- `manifest.json`: per-file SHA-256, original source paths, sizes and provenance.
- `theorem-index.json`: every named theorem with its source module; successive
  namespace blocks are handled correctly.
- `source-to-paper.json`: principal family/module/declaration mapping, all 47
  historical source groups, and every complete module printed in Papers 3 and 4.
- `evidence/`: exact terminal certificate, integrated root and axiom check
  records/logs, source-scope documents and compact closure summary.
- `scripts/`: portable verification and deterministic numerical validation.
- `validation/results.json`: actual numerical outputs, tolerances and driver hash.

## Verify the copied evidence without compiling Lean

From this directory, run:

```sh
python3 scripts/release_verify.py --bundle .
```

This checks file hashes, absence of forbidden proof placeholders, all module
and theorem counts, successive namespaces, membership of every named theorem
in the archived integrated Audit log, and its allowed axiom dependencies.
It does not claim a new Lean run. It requires only Python 3.

## Reproduce the deterministic examples

```sh
python3 scripts/validate_examples.py --output validation/reproduced.json --tex validation/reproduced.tex
```

The driver uses Python's standard library only. It checks balanced-cell roots,
scalar budget reconstruction, homogeneous formulas, a graph with a loop,
parallel edges and passive leaf, the graph deficit, and spectral phase/cosine
assembly. It includes a small nonuniform partition search, explicitly without
certifying the search candidate as the global minimizer. It performs no Monte
Carlo simulation and uses ordinary binary64, not interval arithmetic.

## Reproduce the full Lean checks

Install elan and make `lake` available on PATH. The pinned toolchain is
`leanprover/lean4:v4.33.1`, with Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. Dependency sources/build products
require substantially more storage than this source archive.

Optional dependency cache preparation, from `lean/`:

```sh
lake exe cache get
```

Then, from the bundle directory:

```sh
python3 scripts/release_verify.py --bundle . --lean --memory 4096
```

The script calls pinned Lake's `lake lean FILE -- ...` for every research
source, the root and Audit. Lake builds each file's imports and regenerates
its module setup using the extracted project's local paths. This avoids
copying workstation-specific import-level tables and respects Lean 4.33's
module system. Every target is checked directly, beyond merely compiling a
default Lake target. Calls are sequential, with one Lean thread requested.

The script records a new timestamped report in `reproduction/`, verifies
sources did not change, checks that all named theorems occur in the fresh
transitive audit, and checks the actual clean pinned Mathlib checkout. It
records whether the project had no `.lake` directory when the run began;
it never overwrites the historical certificate. A failed or interrupted run
is not a successful reproduction. The complete run may take substantial time.

## Scope

The source-qualified mathematical claims in all three historical papers are
covered by the 47-group closed ledger. In particular, graph media have at
least one positive-length edge and positive continuous edge conductance and
speed density; unequal density traces at vertices are permitted. Graph local
time has a proved ordinary-length unit-atom Revuz test. Physical graph killing
normalization is identified by the unchanged original weak equation; a new
universal physical graph Revuz correspondence is not claimed. Deterministic
physical-time full-future conditioning and arbitrary reference stopping-time
strong Markov are distinguished from a separate arbitrary physical stopping-
time theorem. See the unabridged certificate qualifications.
