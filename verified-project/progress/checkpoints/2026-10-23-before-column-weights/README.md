# Six vertex formalization

This project audits the original OpenAI six-vertex manuscript and begins its
Lean formalization. The Gaussian free field theorem remains unproved here.

The source is **The Gaussian free field limit of the balanced six-vertex model
with variance multiplier 1/arcsin(c/2)**, dated 23 September 2026 and released in
the October OAI mathematics dump. The downloaded PDF has **93 pages**, including
references.

- [Audit and open verification items](audit/REPORT.md)
- [Progress and next milestones](progress/STATUS.md)
- [Interactive progress map](progress/progress.html)
- [Latest build and axiom audit](progress/verification.json)
- [Source manifest and hashes](sources/openai-math/SOURCE_MANIFEST.json)
- [Lean code](lean/SixVertex.lean)

## Source provenance

The original files come from [openai/math](https://github.com/openai/math), pinned
to commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` (12 October 2026).
The complete, untruncated preprints directory tree at this revision contains one
directory whose name includes “six-vertex”. Its entire PDF and source tree are
preserved under `sources/openai-math/preprints/`, with the original filenames.
The manifest records the source URL, Git blob hash and SHA-256 hash of each file.
There are 15 manuscript files and four repository metadata files. All 19 matched
their pinned repository blob hashes on download.

External literature consulted for the audit is identified separately in the
audit report. It is not presented as part of the OAI dump.

## What is proved

The starter currently proves finite combinatorial results: the six allowed
vertices; ice-rule conservation; arrow-reversal symmetries; periodic balanced
sector conservation; local consistency and uniqueness of four face heights;
soundness and completeness of a glued-column enumerator; transfer-kernel sector
support; and c-free balanced witnesses at every even height.

The transfer kernel is represented by monomial exponents, with an exponent `k`
standing for `c^k`. This is finite combinatorial infrastructure. Enumeration
without duplicates, the finite torus probability law, the matrix trace identity,
and all analytic convergence results remain to be proved.

## Recheck

Requires Lean 4.35.0, Lake, and Python 3. No Mathlib dependency is needed for the
current finite foundations.

```sh
python3 scripts/check.py
python3 scripts/render_progress.py
```

The check builds the library, inspects the axioms of every declared theorem, and
recomputes all downloaded source hashes. The allowed foundational axioms are
`propext`, `Quot.sound`, and `Classical.choice`; `sorryAx` is not permitted.
No axiom standing for an unproved mathematical estimate is added.

## Existing work preserved

`lean/SixVertex/Finite.lean` was adapted from the earlier local scaffold at
`Documents/Codex/2026-10-06/https-github-com-openai-math-tree/outputs/six-vertex-lean`.
The original location was left untouched. Its missing decidability instance for
`TwoIncoming` was supplied, and the file was rebuilt with Lean 4.35.0. The local
height and transfer modules were added for this project.

## Updating progress

`progress/state.json` records milestone statuses and dependencies. Update it only
when there is evidence for a change, then regenerate the display. Build evidence
comes from `progress/verification.json`. The display is a dated snapshot; it does
not run proofs or update itself in the background. See `CONTINUATION.md` for the
next development session.
