# Six vertex progress

Updated 24 October 2026.

**Main result: not proved in Lean.** The library contains 1457 checked Lean theorem declarations. 5 of 51 named paper statements are proved in their stated setting. The helper count is not a percentage of the paper.

**Completed:** [Lemma 2.1, Finite row algebra](../lean/SixVertex/FiniteRowAlgebra.lean), [Lemma 2.3, Single-entry actions](../lean/SixVertex/SingleEntryActions.lean), [Lemma 2.2, Finite Bethe data](../lean/SixVertex/FiniteBetheData.lean), [Lemma 6.2, Convergence of representatives](../lean/SixVertex/ChiralRepresentatives.lean), [Lemma 7.6, Logarithmic integrability](../lean/SixVertex/LogIntegrability.lean). All clauses of these statements are checked. The six-vertex applications of the general representative and measure lemmas remain separate. See [the statement correspondence](named-statements.json).

**Conditional:** [Lemma 2.4, Exact scalar products and deleted columns](../lean/SixVertex/ExactScalarProducts.lean), [Lemma 2.5, The Hilbert dual](../lean/SixVertex/HilbertDual.lean), [Corollary 2.6, Exact finite-word expansion](../lean/SixVertex/ExactFiniteWords.lean), with the sole external assumed input [A01, Slavnov identity](assumptions.json). There are 43 other named statements without complete formalizations.

| Milestone | Status | Next action |
|---|---|---|
| Original OAI sources | complete | Preserve the snapshot; record any future upstream revision separately. |
| Finite model and local heights | in progress | Extend local integration to global simply connected domains. Keep torus winding periods separate. |
| Finite row algebra · Lemma 2.1 | complete | Lemma 2.4 is now verified conditional on the assumed Slavnov identity. Next: Lemma 3.1, Construction and density of the roots. |
| Single-entry actions · Lemma 2.3 | complete | Lemma 2.4 is now verified conditional on the assumed Slavnov identity. Next: Lemma 3.1, Construction and density of the roots. |
| Finite Bethe data · Lemma 2.2 | complete | Lemma 2.4 is now verified conditional on the assumed Slavnov identity. Next: Lemma 3.1, Construction and density of the roots. |
| Scalar products · Lemma 2.4 | conditional | The Hilbert dual is now conditionally verified. Continue with Corollary 2.6, the exact finite-word expectation. |
| The Hilbert dual · Lemma 2.5 | conditional | Continue with the normalized finite-word determinant formula. |
| Finite-word expectations · Corollary 2.6 | conditional | Construct and control finite real roots in Lemma 3.1. |
| Finite probability and transfer | in progress | Construct the multi-column real-valued torus probability law and its transfer trace identity. The named finite row algebra is now proved separately. |
| Roots and thermodynamic bounds | in progress | Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed. |
| Plane law and angular spectrum | queued | Verify the finite folded-block identities and both quotient bounds before constructing the infinite representation. |
| Representative limits · Lemma 6.2 | complete | Apply this lemma once the two-scale tensor representatives and their Gram convergence are constructed. |
| Chiral currents and Wick rule | queued | Prove spectral truncation and the collision limit. Covariance calculations alone do not establish this milestone. |
| Exact variance multiplier | queued | Check finite twist jets and determinant asymptotics, preserving every order of limits. Retain Gaussian convergence as an assumption in the conditional branch. |
| Logarithmic energy · Lemma 7.6 | complete | Use the measure lemma after the smooth-test limit and energy-mollification estimates are proved. Height-field and topology convergence remain open. |
| Height-field convergence | queued | Start with joint convergence on smooth neutral tests; fix the topology before extending the statement. |
| Separate endpoint c = 2 | queued | Prove the exact coupling statement with multiplicities and homogeneous marginals, followed by sign-averaged uniform integrability. |
| Full balanced six-vertex theorem | queued | Close the analytic dependencies and check that the final Lean statement matches the pinned manuscript exactly. |

## Audit

First-pass structural and dependency review complete. 9 verification and scope-clarification items remain open. No mathematical error has been established by this pass. See [the evidence records](../audit/REPORT.md).

## Checks

The build and all-theorem axiom audit passed; all 19 pinned source files were checked against their hashes. See [the machine-readable verification log](verification.json).

The display is a saved snapshot. Re-run the checks and regenerate it after each development milestone.
