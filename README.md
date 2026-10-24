# Six vertex Lean formalization

## Source update 24 October 2026

The supplied [Lean source archive](transfer/sixvertex-lean-sources-2026-10-24.tar) has been applied at its original relative paths: **407 Lean files, 12 additions and 4 changes**. Their contents were copied byte for byte. See [the import record](SOURCE-UPDATE-2026-10-24.json) for filenames and the archive hash.

**This upload did not run Lean, audit proofs, or continue the formalization.** The 1,457-declaration audit, old handover, progress counts, WIP status records and associated logs describe the earlier checkpoint; they are not a verification of these newer sources. The original checkpoint remains available in Git history and the original handover ZIP. `SHA256SUMS` now checks the current repository files; the original manifest is retained in `transfer/`.

Formalization of the pinned OAI six-vertex manuscript, with a historical audited checkpoint, a later source upload and a portable handover. Formalization remains paused at the owner’s request.

## Start here

Read [HANDOVER.txt](HANDOVER.txt) for the full mathematical status, assumptions, setup instructions and next proof obligations.

| Directory | Contents |
| --- | --- |
| [verified-project](verified-project) | Latest supplied sources; the included **1,457-declaration audit** belongs to the earlier checkpoint |
| [work-in-progress](work-in-progress) | Supplied drafts and historical [STATUS.json](work-in-progress/STATUS.json); their current proof status was not assessed during upload |
| [logs](logs) | Check and build output for the newer work |
| [transfer](transfer) | Original portable ZIP and its size/checksum record |

At the earlier audited checkpoint, eight whole named paper statements were complete: Lemmas 2.1, 2.2, 2.3, 6.2 and 7.6 without external mathematical assumptions; Lemmas 2.4 and 2.5 and Corollary 2.6 conditional on the explicitly authorized **A01 Slavnov identity**. Supporting theorem declarations are counted separately. **Lemma 3.1 and the main Gaussian free field limit remain incomplete.**

The earlier audited checkpoint proves that the constructed free Slater state is the actual spin Hamiltonian’s simple ground-state line. Identifying the actual Bethe vector with that line and justifying continuation in lambda remain open. No additional external mathematical assumptions are authorized.

## Verify the transferred files

From this repository’s root:

```sh
python3 verify_bundle.py
```

This checks the current repository files against `SHA256SUMS`, including the supplied source update and transfer archives. It checks file integrity, not mathematical correctness. The original handover ZIP retains the earlier snapshot and its original manifest.

## Build and audit the uploaded Lean project

Install Git, Python 3 and elan, then use the pinned toolchain:

```sh
elan toolchain install leanprover/lean4:v4.35.0
cd verified-project/lean
lake exe cache get
python3 ../scripts/check.py
```

The Lake project root is `verified-project/lean`. Preserve `lake-manifest.json`; mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Dependency caches are downloaded separately. The full checker rebuilds the project, audits every public theorem’s axioms, checks proof placeholders and verifies the 19 original source hashes. Run it locally before claiming the transferred project has been verified on a new machine.

## Original manuscript and provenance

The 93-page original OAI manuscript, TeX sources and provenance records are preserved under [verified-project/sources](verified-project/sources), pinned to source revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. See its source manifest for exact paths and hashes. Original source attribution and notices are preserved.

The progress view is [verified-project/progress/progress.html](verified-project/progress/progress.html); download or open it locally to view it. No GitHub Pages deployment is configured.

## Continue work deliberately

The four individually checked WIP modules are outside the audited root imports. The two unfinished drafts are not proved results. Read the handover before integrating any WIP, and obtain a fresh full audit before reporting a new checkpoint. Historical usage figures in the handover belong to the original account and are not a target for a different account.
