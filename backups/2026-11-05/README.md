# Complete formalization work snapshot — 5 November 2026

This archive is the CURRENT complete project-work backup. The ordinary source tree outside this backup directory remains the older October import.

Contains 10,473 files (439,723,501 uncompressed bytes): all Lean sources, supporting drafts, verification records, continuation records, project scripts, papers and handover files from the entire local Formalization 6V folder. Generated .lake build/dependency caches, .git metadata, Python caches, Finder metadata and .env files are excluded. The existing repository history remains intact. No credentials were detected by the limited pre-upload credential-pattern check.

Verified checkpoint: 25/51 whole named paper statements complete; Proposition 4.3 incomplete. Full audit 377 passed with 10,130 owned public theorem declarations. Owned build 378 passed; full audit 378 not started. The additional two FiniteConditionalEntropySubadditivity supporting results passed their kernel check and are preserved in drafts, not promoted or counted as whole statements.

## Restore

Download all six .part000 through .part005 files in this directory, plus manifest.json. In a terminal in that directory:

```sh
cat Formalization-6V-2026-11-05.tar.gz.part* > Formalization-6V-2026-11-05.tar.gz
shasum -a 256 Formalization-6V-2026-11-05.tar.gz
tar -xzf Formalization-6V-2026-11-05.tar.gz
```

Expected archive SHA-256: `9f24fd433dffba20b5c1ce6b54234ca851bf707bb3e249d01f1808973990e2b7`.

Read the newest verified-project/CONTINUATION.md, progress/active-run.json, and drafts/2026-11-04-proposition43/CURRENT.txt before resuming. Builds require the pinned Lean toolchain and regeneration of .lake dependencies. The backup itself does not claim any additional mathematical verification.
