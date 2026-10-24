# Continue the six vertex project

1. Read the README, audit report, progress state and latest verification result.
2. Preserve the pinned OAI sources. Add any source revision in a separate tree
   with a new manifest; do not silently replace the audited text.
3. Keep paper-proof presence, independent mathematical verification, numerical
   evidence and Lean verification distinct in all progress records.
4. Next prove that the finite-column enumerator has no duplicate configurations,
   construct a weighted finite torus law, and establish its transfer trace
   identity. Handle zero circumference explicitly or restrict the domain.
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
