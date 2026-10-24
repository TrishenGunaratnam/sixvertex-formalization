# Continue the six vertex project

1. Read the README, audit report, progress state and latest verification result.
2. Preserve the pinned OAI sources. Add any source revision in a separate tree
   with a new manifest; do not silently replace the audited text.
3. Keep paper-proof presence, independent mathematical verification, numerical
   evidence and Lean verification distinct in all progress records.
4. Duplicate-free column enumeration and the exact positive-rational
   single-column probability law are proved. Next introduce real coefficients,
   construct the multi-column finite torus law and prove the transfer trace
   identity. At positive height the vertex-list enumeration is duplicate-free;
   height zero retains two distinct seam-spin records. Restrict the physical
   torus statement to its intended positive circumferences.
5. Extend the local height results to global path independence on a simply
   connected domain. Track torus periods separately.
6. Introduce a pinned Mathlib dependency when real weights, finite probability
   and matrix algebra need it. Do not change the current toolchain silently.
7. Begin the analytic audit with the common-radius boundary-division lemma and
   Gaudin/mixed inverse bounds. Each finding in the report specifies a remaining
   proof obligation. Prove a standalone precise version before marking it closed.
8. Run `python3 scripts/check.py` after edits. Record theorem scope, build evidence
   and any remaining assumptions. Regenerate the progress display afterward.
9. No unfinished proof holes or mathematical axioms may count as completed
   results. A conditional result must retain its assumptions in its statement.

The GFF theorem is not formalized. The number of finite helper theorems is not a
percentage of the mathematical work, and no overall completion percentage is used.

## User steering on 23 October 2026

The user deferred `lem:chiral-representatives` as **reasonable to look at later**.
It is not formalized and must not be counted as a proved named statement. No
axiom was added for it. The next proposed candidate is `lem:row-algebra`
(Finite row algebra, Section 2), a collection of model-specific finite-matrix
identities. See `progress/deferred-statements.json` for scope and obligations.
The proposal alone does not complete any part of that lemma.
