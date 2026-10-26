# Lean verification of the double coset paper

The current verification package is **[DCPv7-minimal.zip](DCPv7-minimal.zip?raw=true)**,
for *The double coset problem for parabolic subgroups of braid groups*,
by Arkadius Kalka, Mina Teicher and Boaz Tsaban.

It is **complete modulo 20 explicitly named cited mathematical inputs** and the
standard Lean foundations. The exact assumptions are documented in `TRUST.md`
and audited by Lean. The cited papers' own proofs are outside this boundary.

The source archive contains only the material specific to this verification:

- 75 required custom Lean source modules (including the minimal public wrapper).
- Six verification checks and a small separate consumer package.
- The current manuscript, coverage/provenance metadata, dependency lockfiles,
  a verification script, and a fresh matching-source receipt.
- Instructions and upstream links for obtaining the external dependencies.

**Lean, Mathlib, their transitive dependencies, compiled libraries and caches
are not included.** The archive has 98 files and is 183,527 bytes compressed.
The custom proof modules are unchanged copies from the verified development;
unneeded development helpers and historical logs/receipts are omitted.

## Reproduce

Install [elan](https://github.com/leanprover/elan#installation), Git and Python 3.9
or later. Download and extract the archive, then run:

```sh
cd DCPv7-minimal
lake exe cache get
python3 verify.py
```

The package pins **Lean 4.33.0** and **[Mathlib commit
db584cd6d46c92f209a44c0f1c829460d327499d](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d)**.
Lake obtains the pinned standard packages from their upstream repositories;
Mathlib's cache command obtains the compiled dependencies. See the archive's
`README.md` for reusing an existing shared Mathlib installation and for all checks.

A successful full check writes `verification/result.json`. It builds the proofs
with warnings as errors, checks all 11 labelled manuscript items and five
additional obligations, audits all custom declarations and every DCPv7-origin
declaration, tests full Mathlib in both import orders, checks the independent
consumer, and freezes all input hashes. Post-build checks use up to three
parallel processes by default.

## Verified source

- Fresh package verification: **2026-10-26T22:24:49.203444+00:00**.
- Bundled manuscript SHA-256:
  `4ed2b4de7dcc154f5d8d0a18433c693616e79737f3236d6dd373ccd4f64f0177`.
- Archive SHA-256: `28014f312f5ff9d691cf84220f9a12455c9746df4f3158cbf771618745ef11c1`.
- The strict manuscript audit checked **1,370 declarations from 45 DCPv7-origin
  modules**. Their observed dependencies are exactly the 20 named mathematical
  inputs and the three Lean foundations. The three older direct spherical
  algorithm axioms present in legacy files are forbidden dependencies of
  every DCPv7-origin declaration.

This package targets the included `DCPv7.tex`, including the four authorized
wording/precision corrections recorded in its provenance file. The other
pre-existing DCP5/DCP9 files in this repository are historical snapshots; use the
archive above for the current manuscript and reproduction instructions.
