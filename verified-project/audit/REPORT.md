# Six vertex proof audit

The 93-page OAI manuscript has been checked for its proof structure, source provenance, key external dependencies and selected delicate implications. The first pass establishes **no mathematical error**; it leaves **9 verification and scope-clarification items open**. These flags identify arguments to check, rather than declaring their conclusions false.

The full-range Gaussian free field claim is not independently validated or formalized by this project.

## Scope and source

First-pass dependency and proof-location audit, with targeted checks. This is not a line-by-line independent validation of all analytic estimates.

Source: the October OpenAI mathematics dump, commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The PDF and all source files were downloaded directly from this revision; all 19 manuscript and repository-metadata files match the recorded Git blob and SHA-256 hashes. The directory scan found one manuscript title containing six-vertex. External papers below are reference checks, not alternative OAI source files.

## Proof structure checks

The TeX sources contain **51 named theorem, lemma, proposition or corollary statements** and **286 labels**. The structural scan found no duplicate labels, unresolved internal references, or missing bibliography keys. Presence of text under a proof environment is not verification of the proof.

The four statements not followed immediately by a proof have deferred proofs: the main theorem in `08-main-proof.tex`; covariance normalization later in `05-normalization.tex`; the overlap asymptotic in that section's symbol calculation; and endpoint rotation later in `09-endpoint-rotation.tex`. They are not missing merely because the proofs are deferred.

| Section | Named statements | First-pass review focus |
|---|---:|---|
| [01-introduction.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/01-introduction.tex) | 1 | Exact law, height normalization, test classes and parameter range |
| [02-finite-rows.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex) | 6 | Gauge/adjoint conventions, Bethe data and cited determinant normalization |
| [03-thermodynamic-kernels.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex) | 7 | Sparse roots, uniform inverses, normalization and joint determinant tails |
| [04-angular-plane.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/04-angular-plane.tex) | 8 | Boundary continuation, physical-law identification, orbit measures and Hamiltonian |
| [05-normalization.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/05-normalization.tex) | 5 | Twist stiffness, infrared comparison, overlap jets and sampled symbol |
| [06-chiral-gaussianity.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/06-chiral-gaussianity.tex) | 7 | All-zero control, representative convergence, collision and Wick recursion |
| [07-probabilistic-endgame.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/07-probabilistic-endgame.tex) | 12 | Moment bounds, desmoothing, finite-energy tests and distinct function-space claims |
| [08-main-proof.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/08-main-proof.tex) | 0 | Assembly order and conditional external normalization |
| [09-endpoint-rotation.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/09-endpoint-rotation.tex) | 5 | Fair-signed FK correspondence, homotopy coupling, multiplicity and endpoint closure |

## Evidence labels

- **Checked in Lean:** the precisely described result compiles and its dependencies pass an axiom audit.
- **Checked in Lean conditional:** consequences compile with the explicitly recorded Slavnov hypothesis; the external identity itself remains assumed.
- **Citation checked:** the external source really states the required kind of result, with its range and assumptions; its proof is not thereby revalidated.
- **Proof located and open:** an argument is written in the manuscript, but its delicate implications still need independent verification.

## Findings and remaining obligations

### V01 Arrow convention and local height consistency

**Status:** Checked in Lean within the stated scope. **Priority:** foundation.

**Location:** [sections/01-introduction.tex:22](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/01-introduction.tex#L22), `Height convention`.

**Question:** Does the two-in/two-out rule give the stated unit height increments, with consistent signs?

**Evidence:** The starter Lean code proves equivalence of the ice rule and two incoming arrows; equivalence with zero elementary height circulation; construction and uniqueness of four adjacent face heights with a chosen anchor; and periodic-column sector conservation.

**Remaining work:** Global integration over a simply connected domain, the infinite planar law and torus winding periods remain outside these local proofs. No full paper theorem is certified by this check.

### V02 Complete finite row algebra (Lemma 2.1)

**Status:** Checked in Lean within the stated scope. **Priority:** named paper lemma.

**Location:** [sections/02-finite-rows.tex:75](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L75), `lem:row-algebra`.

**Question:** Do all gauge, adjoint, RTT, mark-exchange, commuting-row and endpoint identities hold with the displayed conventions?

**Evidence:** The theorem SixVertex.finite_row_algebra proves every clause from the explicit complex matrices. Its helper proofs cover all even chain lengths, real inhomogeneities and arbitrary complex spectral arguments. Commutation at singular intertwiner differences is obtained by a proved analytic-continuation argument. The named statement uses 0 < lambda < pi and even L >= 4, as in Section 1 line 16. The complete library has 776 theorems and passes the build and all-theorem axiom audit. No mathematical mistake was found in this lemma.

**Remaining work:** Five named statements are now unconditional and three conditional on A01; 43 other named statements remain without complete formalizations. The finite row lemma does not establish a thermodynamic or GFF limit.

### V03 Complete single-entry actions (Lemma 2.3)

**Status:** Checked in Lean within the stated scope. **Priority:** named paper lemma.

**Location:** [sections/02-finite-rows.tex:309](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L309), `lem:finite-actions`.

**Question:** Do all four action formulas, the ordered C coefficients, word paths and coincident limits hold for the actual standard monodromy?

**Evidence:** The theorem SixVertex.single_entry_actions assembles every clause. The full library has 776 checked theorem declarations and passes its build and axiom audit. The C coefficient is proved by an independent extra-site block argument from the A/L formulas; no vacuum eigenvalue is divided out. Finite-word paths and the cardinality bound are proved for every word length. A filter-limit theorem proves the complete expression at coincident arguments with labelled multiplicities.

**Remaining work:** No mathematical error was found in this lemma. The manuscript proof divides by generic vacuum factors; its prefatory continuation convention handles their zeros. The Lean proof includes those zeros directly. The Slavnov determinant remains an explicit external assumption A01; its finite scalar-product consequences are now conditionally formalized. All infinite-volume estimates and the GFF theorem remain open.

### V04 Complete finite Bethe data (Lemma 2.2)

**Status:** Checked in Lean within the stated scope. **Priority:** named paper lemma.

**Location:** [sections/02-finite-rows.tex:200](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L200), `lem:bethe-data`.

**Question:** Do the counting phase, eigenvector normalization, moving-root Jacobian, analytic branch and finite Gaudin positivity hold with the paper conventions?

**Evidence:** SixVertex.finite_bethe_data proves every clause. Its helpers prove the explicit odd primitives and phase, the on-shell cancellation, the exact physical (-1)^n factor, an entire eigenvalue extension, the full counting Jacobian, a real analytic local root branch with its twist derivative, positive definiteness for lambda >= pi/2, and the weighted matrix identity. All 776 theorem declarations pass the complete build and axiom audit.

**Remaining work:** No mathematical mistake was found in this lemma. Positive definiteness and local analytic continuation supply no estimate uniform in chain length. The thermodynamic root construction, Gaudin/mixed inverse bounds, unconditional Slavnov identity and GFF theorem remain open. The eight analytic audit flags remain open.

### V05 Exact scalar products and deleted columns (Lemma 2.4), conditional on Slavnov

**Status:** Checked in Lean conditional on the explicit assumed statement A01. **Priority:** named paper lemma.

**Location:** [sections/02-finite-rows.tex:422](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L422), `lem:scalar-product`.

**Question:** Do the norm, source limits, determinant replacements and Gaudin weights follow with the exact stated normalizations?

**Evidence:** SixVertex.exact_scalar_products_and_deleted_columns compiles with hSlavnov : SlavnovIdentity as its one explicit external hypothesis, authorized by the user. The independent root derivative and its source normalization, full complex source-Gaudin limit, vacuum residues, simultaneous pole cancellation, exact norm/nonvanishing, arbitrary deleted-column minors, weights and complete-expression coincident limits are proved. All 776 theorem declarations pass the build and axiom audit; no global mathematical axiom or unfinished proof was added.

**Remaining work:** Discharge A01, the twisted Slavnov identity, to make this lemma unconditional. Five named lemmas are unconditional; three statements are verified conditional on A01; 43 other named statements remain without complete formalizations. All eight analytic audit flags remain open.

### V06 The Hilbert dual (Lemma 2.5)

**Status:** Checked in Lean conditional on the explicit assumed statement A01. **Priority:** named paper lemma.

**Location:** [sections/02-finite-rows.tex:528](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L528), `lem:hilbert-dual`.

**Question:** Does the algebraic scalar product equal the physical Hilbert product with the stated signs, normalization and two-orientation overlap?

**Evidence:** SixVertex.hilbert_dual assembles all clauses. The adjoint, real-root creation-list duality, physical gauge isometry and exact norm identity are unconditional on Slavnov. Nonvanishing and unit normalization use the existing A01 hypothesis; the overlap includes two root lists with possibly different twists. SpinHilbert uses the actual L2 norm. All 776 theorem declarations pass the build and axiom audit. Exact spin-sector conservation and initial upper/lower path-quotient identities are also proved as preparation for Corollary 2.6.

**Remaining work:** A01 remains assumed. The Hilbert-dual lemma and Corollary2.6 are both now fully checked conditional only on A01. The eight analytic audit flags remain open.

### R01 Balanced plane law and zero-slope identification for c at least one

**Status:** Cited statement located and checked; external proof not formalized. **Priority:** resolved citation question.

**Location:** [sections/04-angular-plane.tex:290](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/04-angular-plane.tex#L290), `prop:physical-plane`.

**Question:** Is uniqueness being inferred merely from zero expected slope?

**Evidence:** No. The manuscript includes a variational-domain and ergodic-component argument. DKLM arXiv:2603.06268v1, Theorem 2.2 and the paragraph following equation (6), explicitly identify the balanced limit and describe it as a unique free-energy minimizer for the stated range. Lammers-Tassy arXiv:2004.15025v1, Theorem 13.16, states the six-vertex strict-convexity condition c+ c- >= max(a+ a-, b+ b-), matching c >= 1 when a=b=1.

**Remaining work:** Formalize the precise variational functional and the domain-reduction argument, or import fully proved versions. Checking the citation statement is not re-proving the external result.

References: [2603.06268v1](https://arxiv.org/html/2603.06268v1), [2004.15025v1](https://arxiv.org/html/2004.15025v1).

### R02 Conditional normalization does not supply Gaussian convergence

**Status:** Cited statement located and checked; external proof not formalized. **Priority:** resolved citation question.

**Location:** [sections/08-main-proof.tex:39](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/08-main-proof.tex#L39), `Final use of DKLM Theorems 4.3 and 4.4`.

**Question:** Does the proof assume its desired GFF limit when identifying the variance?

**Evidence:** The final proof invokes normalization after the preceding sections establish a GFF limit with undetermined coefficient. DKLM Theorem 4.3 explicitly assumes a subsequential GFF limit; Theorem 4.4 computes the free-energy curvature. Both state c in [1,2]. The manuscript uses a separate stiffness/overlap argument for c<1.

**Remaining work:** Preserve this dependency order in Lean. Theorem 4.3 cannot be used to establish Gaussianity, and its range cannot be extended below c=1 without another proof.

References: [2603.06268v1](https://arxiv.org/html/2603.06268v1).

### R03 The cited twisted scalar-product identity exists

**Status:** Cited statement located and checked; external proof not formalized. **Priority:** resolved citation question.

**Location:** [sections/02-finite-rows.tex:423](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L423), `lem:scalar-product`.

**Question:** Is the determinant formula actually supplied by the cited source?

**Evidence:** KMST arXiv:hep-th/0406190v1, Proposition 3.1 and equations (3.8)-(3.9), give the derivative-over-Cauchy determinant formula for a twisted on-shell vector and generic off-shell variables. The manuscript explains its monodromy rescaling and compensating twist factor, then treats coincident columns separately.

**Remaining work:** A01 remains externally assumed. Lemma 2.4 now proves the source rescaling, independent-root derivative normalization, slot order, complex pole limits and deleted-column specializations conditional on that exact identity. Discharging A01, including all parameter specializations in the physical range, remains future work.

References: [0406190v1](https://arxiv.org/html/hep-th/0406190v1).

### U01 Uniform Gaudin and mixed-measure bounds

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/03-thermodynamic-kernels.tex:480](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L480), `lem:gaudin-inverse`.

**Question:** Why do inverses stay bounded when the terminal Bethe roots become sparse?

**Evidence:** A proof is present. It separates contracting dense rows from finitely many edge indices, extracts a one-sided limiting equation, and uses a decaying maximum-principle argument. The mixed operator is undressed into a positive-measure equation. Thus this is not justified merely by finite nonsingularity or diagonal dominance.

**Remaining work:** Verify uniform edge-index bounds and local mass; passage to the extracted equation including tails; existence of a nonzero limiting coordinate; and the weighted perturbation bounds, in each declared order of limits. State a lower-bound theorem separately from an invertibility theorem on infinite-dimensional spaces.

### U02 Joint determinant tails and exchanges of infinite-volume limits

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/03-thermodynamic-kernels.tex:918](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L918), `lem:weighted-flags; lem:joint-determinant-tails; prop:word-kernel`.

**Question:** Are simultaneous root escapes controlled strongly enough to sum the finite-word expansion?

**Evidence:** The weighted-flags lemma is followed by a joint-minor estimate and a locally uniform word-kernel limit. The proof adapts separate flag bases for positive and negative minors, extracts quadrature weights, and claims an exponential majorant. The array limit is explicitly lim(d->0) limsup(B->infinity), rather than an asserted limit at every fixed d.

**Remaining work:** Check residue codimensions, nested flag dimensions, uniform constants and all near-coincidence cancellations. Construct the majorizing measure and prove dominated convergence before using the resulting word kernels. Fixed-word estimates must not be used for unbounded word length.

### U03 A common analytic radius at boundary rows

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/04-angular-plane.tex:98](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/04-angular-plane.tex#L98), `lem:scalar-continuation`.

**Question:** Does finite invertibility near a swap point give a radius independent of lattice size?

**Evidence:** The manuscript provides a folded two-auxiliary block calculation, a geometric bound on its complementary block, quotient bounds, then a wordwise continuation and a countable fiber construction. The preceding harmonic-row-normalization lemma separately handles vacuum denominator zeros inside the strip.

**Remaining work:** Prove the displayed finite folded-block identities, both left and right quotient bounds and their uniform constants. Verify passage from word-dependent norm bounds to one scalar continuation radius on a common full-measure set. Finite analyticity alone is insufficient.

### U04 Covariance normalization below c=1

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/05-normalization.tex:77](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/05-normalization.tex#L77), `lem:stiffness; lem:infrared; lem:overlap-asymptotic; lem:detector-packing`.

**Question:** Are the twist derivatives and determinant asymptotics justified before the limits?

**Evidence:** There are separate lower and upper bounds for the orbit mass. The stiffness uses fixed-filling finite derivatives; the upper bound uses the finite twist-overlap Taylor coefficient, then a finite-trace analysis and a sampled symbol. The text explicitly takes Taylor coefficients before either array limit and supplies the deferred overlap proof later in the section.

**Remaining work:** Re-derive the finite second-derivative identities, uniform root jets, inverse-row estimates, end corrections and Fourier/sampling calculation. Verify that no derivative of a limiting free energy is substituted for the required limit of finite derivatives. This is a central unverified analytic dependency.

### U05 Two-scale spectral convergence needs all zeros controlled

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/06-chiral-gaussianity.tex:231](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/06-chiral-gaussianity.tex#L231), `prop:two-scale`.

**Question:** Could zeros between the two observed scales alter the rescaled energies?

**Evidence:** The manuscript addresses this explicitly with an exterior-dip bound, an all-zero exceptional-event bound, fixed annular windows and a zero-count truncation before sending the mesh to zero. It defines representative convergence rather than asserting a bounded embedding of the whole tensor completion.

**Remaining work:** Verify the state-measure exceptional-event estimate, the zero-count truncation, discontinuity-free spectral cutoffs and strong convergence on representatives. Compact-open convergence of spectral functions alone does not imply the claimed energy limits.

### U06 Gaussianity requires the nonvacuum collision lemma

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/06-chiral-gaussianity.tex:668](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/06-chiral-gaussianity.tex#L668), `lem:collision; prop:gaussian-currents`.

**Question:** What establishes Wick's rule beyond two-point covariance?

**Evidence:** The collision lemma claims weak convergence of a damped two-current operator to -kappa times the identity, including nonvacuum exterior states. It uses another scale separation, contour formulas and uniform dyadic cutoff removal. The subsequent proposition removes artificial poles, rules out a simple collision residue, and derives Wick recursion.

**Remaining work:** Prove the collision operator limit, its uniform norm majorant and the interchange with strongly converging exterior vectors. Verify joint holomorphy and moving-pole removal. This is the central Gaussianity obligation; knowing the variance is insufficient.

### U07 Nonsmooth tests and negative function-space conventions

**Status:** Proof located; independent verification remains open. **Priority:** medium.

**Location:** [sections/07-probabilistic-endgame.tex:558](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/07-probabilistic-endgame.tex#L558), `lem:log-integrability; prop:finite-energy; prop:negative-regularity; prop:intrinsic-dual`.

**Question:** Do the smooth-test limit and logarithmic bounds imply every advertised topology?

**Evidence:** Separate proofs are supplied for finite-energy measures, restriction Besov/Hölder/Sobolev norms, the source's outward-scaling completion, and intrinsic Sobolev duals on arbitrary bounded open sets. The finite-energy proof includes the case where distinct continuum points round to the same lattice face. The intrinsic proof treats small-area cells by a thick/thin decomposition. Lemma 7.6 is now fully checked in Lean, including the mixed absolute logarithmic integral and atomlessness; the other analytic and topological obligations remain open.

**Remaining work:** Fix exact definitions of each negative Sobolev realization before formalization. Independently check logarithmic domination, mollification in energy, separability, compactness, pinning and thin-cell estimates. The phrase 'usual ... realization' needs an explicit definition; these spaces must not be silently identified on irregular domains.

### U08 Endpoint rotation requires a loop bijection, not just close loop sets

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/09-endpoint-rotation.tex:276](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/09-endpoint-rotation.tex#L276), `lem:rr-nails; thm:rr-rotation; prop:endpoint-completion`.

**Question:** Does the external FK rotation argument preserve multiplicity and endpoint separation information?

**Evidence:** The appendix deliberately uses the homotopy coupling before its metric conclusion. The cited rotation paper, arXiv:2012.11672v2, Definition 3.8 and Sections 3.5-3.6, does define homotopic similarity using a bijection of nontrivial loops and matching crossing words. Lis arXiv:2004.05337v2, Lemma 3.1, supplies the stated infinite-volume loop-law convergence at c=2. The OAI appendix includes fair-sign averaging, loop counts, point avoidance and a nail-window extraction.

**Remaining work:** Verify the full extracted coupling with its exact marginals, parameter scales, orientations and multiplicities; the inside/outside transfer; and uniform integrability of the sign-averaged polynomial. The external set-distance rotation theorem alone would not prove this step. The complete extraction is not independently verified here.

References: [2012.11672v2](https://arxiv.org/html/2012.11672v2), [2004.05337v2](https://arxiv.org/html/2004.05337v2).

### V07 Exact finite-word expansion (Corollary 2.6)

**Status:** Checked in Lean conditional on the explicit assumed statement A01. **Priority:** named paper corollary.

**Location:** [sections/02-finite-rows.tex:620](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L620), `cor:finite-word-expansion`.

**Question:** Does the complete physical marked-word expectation equal the exact bounded-size determinant path sum, with all parity and pair factors?

**Evidence:** All clauses are assembled in SixVertex.exact_finite_word_expansion. Arbitrary marks, normalized unit physical vectors, source/vacuum cancellation, weighted minors, spin selection, replacement slots, size bound, diagonal parity and every ordered removal history are proved. No sorry or new global axiom. The only assumed identity is A01.

**Remaining work:** The exact finite formula is checked conditional only on A01. The thermodynamic application and GFF limit remain open;see V08 for the current root and measure formalization boundary.

### V08 Finite root construction foundations (Lemma 3.1, partial)

**Status:** Partially checked in Lean; full statement open. **Priority:** next named paper lemma.

**Location:** [sections/03-thermodynamic-kernels.tex:78](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L78), `lem:root-limits`.

**Question:** Can the starting roots, parameter continuation and no-escape steps be verified without assuming existence or compactness?

**Evidence:** 1233 declarations pass the full build and axiom audit. Fixed-length actual mass removes the finite local-density cutoff. A joint actual-root certificate and universal family selection assemble all measure and analytic conclusions for the same roots. Actual measure convergence follows in occupied windows. See V82-V84;U09 remains a scope clarification.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V09 Exact kernel mass and exponential decay

**Status:** Checked in Lean within the stated scope. **Priority:** supporting analytic estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:15](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L15), `Full-line kernel preliminaries`.

**Question:** Is the claimed L1 contraction constant actually proved from the kernel formula?

**Evidence:** KernelDecay.lean proves an explicit exponential bound for every physical lambda. KernelMass.lean proves integrability, integral K = 1-2*lambda/pi, integral abs K = abs(1-2*lambda/pi) < 1, and integral s = 1-lambda/pi. No external identity is assumed.

**Remaining work:** The actual full-line resolvent, its first derivative and counting-discrepancy applications are checked, as is the actual finite-window inverse. All-orders, discrete Gaudin and mixed-measure inverse estimates remain open.

### V10 Convergence of representatives, Lemma 6.2

**Status:** Checked in Lean within the stated scope. **Priority:** complete named statement.

**Location:** [sections/06-chiral-gaussianity.tex:201](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/06-chiral-gaussianity.tex#L201), `lem:chiral-representatives`.

**Question:** Do bounded core limits extend, compose and obey the pairings-plus-norm criterion without a global representative map?

**Evidence:** ChiralRepresentatives.lean proves all three clauses in arbitrary dense representative systems with Gram convergence. The full build and all-theorem axiom audit pass. There is no external assumption.

**Remaining work:** The preceding six-vertex tensor construction and Gram convergence are separate unformalized dependencies of its application; no chiral-current or Wick limit is claimed.

### V11 Logarithmic integrability, Lemma 7.6

**Status:** Checked in Lean within the stated scope. **Priority:** complete named statement.

**Location:** [sections/07-probabilistic-endgame.tex:558](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/07-probabilistic-endgame.tex#L558), `lem:log-integrability`.

**Question:** Does ordinary finite self energy exclude atoms and imply finite mixed absolute logarithmic energy?

**Evidence:** All 776 theorems pass the full build and axiom audit. LogIntegrability.lean proves no atoms, finite self absolute energy and finite mixed energy. It retains the infinite diagonal and proves the bridge to ordinary integrability. The dyadic square geometry and every infinite-sum bound are checked; no external estimate is assumed.

**Remaining work:** This closes the standalone measure lemma, not the smooth-test limit, energy mollification, pinning, thin-cell estimates or function-space convergence.

### V12 Half-filled counting discrepancy and density regularity

**Status:** Checked in Lean within the stated scope. **Priority:** supporting estimates for Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:161](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L161), `eq:counting-sawtooth`.

**Question:** Are the counting primitive, the 1/2 bound and the logarithmic density derivative actually proved for finite consecutive roots?

**Evidence:** CountingMass and CountingSawtooth prove the total mass n, cumulative integrals, the actual empirical-measure primitive, uniform |F_L| <= 1/2 and zero limits at both ends. DensityRegularity proves the genuine derivative, |rho_prime| <= C_lambda rho, exponential density comparison and the uniform root atom-weight bound. No root density asymptotics are assumed. The uniform half-filled density discrepancy rho_L-p_L is proved, with constants depending only on lambda, for every real site array and every finite half-filled consecutive root list. The function p_L is proved exactly equal to the sum of translates of the inverse-defined full-line density. Full-line convolution integration by parts, the actual root jump identity, Fubini associativity and the inverse representation I-R0* are also proved. The integrated discrepancy is still in progress; Lemma 3.1 remains incomplete.

**Remaining work:** The actual first-derivative representation, first-item discrepancies, negative-K sparse-edge estimates and finite-window inverse/reference construction are checked. The full Lemma3.1 remains partial. Quantitative correction to on-shell roots, weighted Gaudin/mixed estimates, explicit r evaluation and exponential deficit, lower/positive-K comparisons, nominal edges and sector Perron identification remain open.

### V13 Weighted Neumann inverses and the actual full-line resolvent kernel

**Status:** Checked in Lean within the stated scope. **Priority:** supporting analytic construction.

**Location:** [sections/03-thermodynamic-kernels.tex:15](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L15), `Full-line kernel preliminaries`.

**Question:** Does the Neumann argument construct a genuine integrable resolvent kernel with an integrable first derivative?

**Evidence:** BoundedConvolution constructs real convolution on bounded continuous functions and both inverse identities with the quantitative norm bound. WeightedKernel proves a positive exponential weight with mass below one by dominated convergence. WeightedConvolution proves uniform signed-weight inverses. WeightedResolvent and ResolventKernel construct and uniquely identify an exponentially decaying continuous integrable kernel solving R+K*R=K. ConvolutionDerivative proves its genuine first derivative and L1 integrability by differentiation under the integral. All are built from the physical hyperbolic kernel without an external mathematical assumption. Fubini associativity is now checked and the actual inverse is proved equal to I-R0* on bounded continuous functions.

**Remaining work:** Counting-discrepancy applications and finite-window inverses are now checked in later blocks. This full-line result alone makes no all-orders, discrete Gaudin or mixed-measure inverse claim.

### V14 Half-filled roots and both uniform density discrepancies

**Status:** Checked in Lean within the stated scope. **Priority:** complete item of a partially formalized named statement.

**Location:** [sections/03-thermodynamic-kernels.tex:84](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L84), `lem:root-limits, first item`.

**Question:** Are both actual density discrepancies uniformly bounded for arbitrary finite half-filled real arrays?

**Evidence:** The complete first item of Lemma 3.1 is proved with constants fixed before every chain length and real site array: finite distinct zero-twist roots, positive density, uniform rho_L-p_L and ordinary half-line integrated discrepancy. The comparison p_L is exactly the sum of translates of r with its primary inverse-operator definition. The separate hyperbolic closed-form evaluation of r is not asserted. The actual dressed source is integrable, has mass L/2, and has a checked cumulative primitive. The remaining items and Perron clauses of Lemma 3.1 remain open.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V15 Edge-index densities, reciprocal weights and terminal gaps

**Status:** Checked in Lean within the stated scope. **Priority:** supporting sparse-edge estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:188](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L188), `eq:edge-index-density and surrounding gap estimates`.

**Question:** Do the actual finite roots have the quantitative edge density/weight and gap bounds needed for the one-sided inverse argument?

**Evidence:** The strict negative-kernel sparse-edge estimates are now checked: positive physical kernel tail envelopes, value/tail comparison, exact inward/outward counting-tail partition, the own-root half-mass deficit, density comparable to the right-edge index, reciprocal density comparable to the inverse index, a positive adjacent-gap lower bound, and a uniform adjacent-gap upper bound when the inner root lies beyond every bare center. All constants are fixed before the real arrays and chain lengths.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V16 Actual quadrature-measure local mass at every negative-kernel filling

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:111](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L111), `lem:root-limits, third-item local mass`.

**Question:** Can the actual inverse-density atomic measure be uniformly bounded locally without unproved edge-location asymptotics?

**Evidence:** Uniform unit-interval mass is proved for the actual positive atomic quadrature measure nu_L for every strict negative-kernel consecutive root list, every filling and every real site array. The constant is fixed before all chains and intervals. The proof uses a local consecutive-level root count, the actual logarithmic density bound and the own-root contribution -K(0), without a density asymptotic or nominal-edge premise.

**Remaining work:** Negative-K bounded-Lipschitz quadrature is now checked on occupied counting windows (V17), with the half-filled C/L regime derived (V18). Positive-K near-half filling and regular-filling quantile/occupied-window identification remain open.

### V17 Actual bounded-Lipschitz quadrature on occupied windows

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:425](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L425), `lem:root-limits, third-item quadrature`.

**Question:** Does the actual root measure satisfy the stated Lipschitz error, with its filling and support conditions explicit?

**Evidence:** The actual inverse-density atomic measure has a checked compact bounded-Lipschitz quadrature error at most (z-a)*(Lip(phi)+C_lambda*norm(phi))/(2*M) on any occupied counting window where the actual density is at least M>0. The proof uses the local counting sawtooth, absolutely continuous integration by parts, the actual a.e. Lipschitz derivative, and a clamped reciprocal density; it does not assume a smoothing theorem or a positive lower density at infinity. At half filling the window condition is automatic.

**Remaining work:** The whole Lemma 3.1 remains incomplete: finite-interval comparison, mass defect and quantile stability including positive K, explicit hyperbolic density evaluation, nominal edges and Perron identification remain open.

### V18 Half-filled local density growth and C/L convergence

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:425](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L425), `lem:root-limits, third-item quadrature`.

**Question:** Does the actual root measure satisfy the stated Lipschitz error, with its filling and support conditions explicit?

**Evidence:** For uniformly bounded real site arrays, the actual negative-kernel density on a fixed compact interval is at least d*L with d>0 fixed before all chains. This gives a uniform C/L quadrature rate for all unit bounded-Lipschitz tests on that interval, and their integrals against the actual half-filled root measures converge to ordinary Lebesgue integrals along any half-filled chain-length sequence tending to infinity.

**Remaining work:** The whole Lemma 3.1 remains incomplete: finite-interval comparison, mass defect and quantile stability including positive K, explicit hyperbolic density evaluation, nominal edges and Perron identification remain open.

### V19 Actual finite-interval integral operator and uniform inverse

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:256](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L256), `lem:root-limits, second-item finite interval`.

**Question:** Are the finite-interval inverse, signs and masses derived from the actual kernel integral rather than assumed?

**Evidence:** For every physical lambda and every Q, the actual kernel integral over [-Q,Q] defines a bounded-continuous operator with norm at most h=norm(K)_1<1. Both Neumann inverse identities and a uniform (1-h)^(-1) norm bound are checked. The actual r_Q and H_Q, their integral equations and uniqueness are defined and proved. The window operator is Lipschitz in nonnegative Q in operator norm.

**Remaining work:** The full named Lemma3.1 remains partial. The explicit hyperbolic/Fourier evaluation, lower r_Q comparison, positive-kernel comparison, exponential mass defect, quantitative quantile stability, nominal edges and sector Perron identification remain open.

### V20 Negative-kernel finite-interval positivity and comparisons

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:268](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L268), `lem:root-limits, second-item finite interval`.

**Question:** Are the finite-interval inverse, signs and masses derived from the actual kernel integral rather than assumed?

**Evidence:** For lambda>=pi/2, the actual negative-kernel Neumann series preserves positivity. It proves r_Q>=s>0, 1<=H_Q<=(1-h)^(-1), r_Q<=r and monotonicity of r_Q with Q, on their bounded whole-line extensions. Here r retains its primary inverse-defined meaning; the hyperbolic formula and the lower bound c*r<=r_Q are not asserted.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V21 Finite-interval filling mass and endpoint exhaustion

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma 3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:363](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L363), `lem:root-limits, second-item finite interval`.

**Question:** Are the finite-interval inverse, signs and masses derived from the actual kernel integral rather than assumed?

**Evidence:** The actual r_Q extension is L1. Fubini gives its ordinary total-mass equation. In the negative-kernel regime M_Q=integral[-Q,Q]r_Q is monotone, equals0 at Q=0, lies in(0,1/2) for Q>0 and tends to1/2. Its deficit is between the actual exterior mass of r and that mass divided by2*(1-lambda/pi). Thus any endpoint family whose filling masses tend to1/2 must tend to infinity. No exponential defect rate or positive-kernel comparison is assumed.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V22 Actual endpoint and filling-mass continuity

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:363](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L363), `lem:root-limits, reference cutoff`.

**Question:** Can Q be selected by the actual filling mass without assuming its continuity?

**Evidence:** The actual finite-window resolvent source identity proves one Lipschitz constant for r_Q over all Q>=0. Consequently the ordinary filling mass M_Q is Lipschitz and continuous on each bounded nonnegative cutoff interval, for every physical lambda. In the negative-kernel regime, every rho in(0,1/2) has an actual Q>0 with M_Q=rho, by the proved half-mass limit, M_0=0 and the intermediate value theorem. This proves reference cutoff existence, not cutoff uniqueness or reference/on-shell quantile stability.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V23 Reference cutoff existence at every negative-kernel filling

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:104](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L104), `lem:root-limits, reference cutoff`.

**Question:** Can Q be selected by the actual filling mass without assuming its continuity?

**Evidence:** The actual finite-window resolvent source identity proves one Lipschitz constant for r_Q over all Q>=0. Consequently the ordinary filling mass M_Q is Lipschitz and continuous on each bounded nonnegative cutoff interval, for every physical lambda. In the negative-kernel regime, every rho in(0,1/2) has an actual Q>0 with M_Q=rho, by the proved half-mass limit, M_0=0 and the intermediate value theorem. This proves reference cutoff existence, not cutoff uniqueness or reference/on-shell quantile stability.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V24 Actual unique and ordered finite reference quantiles

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:383](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L383), `lem:root-limits, reference quantiles`.

**Question:** Are the actual reference quantiles normalized correctly, and is their finite Bethe residual bounded independently of chain length and cutoff?

**Evidence:** The actual cumulative integral of r_Q has derivative r_Q, is continuous and strictly increasing for lambda>=pi/2. Every interior level has a unique point in(-Q,Q). Actual ordered mid-quantiles with exact L*cumulative=j+1/2 equations exist for each selected negative-kernel sub-half-filled cutoff; the entire reference configuration is constructed for every finite0<n<L/2.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V25 Finite reference quadrature with endpoint cancellation

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:386](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L386), `lem:root-limits, reference quantiles`.

**Question:** Are the actual reference quantiles normalized correctly, and is their finite Bethe residual bounded independently of chain length and cutoff?

**Evidence:** Finite discrete/smooth integration by parts is checked with its endpoint terms. They cancel when the root list and actual density primitive have the same mass. The local C1 error is at most one half of the derivative integral on the interval; the global derivative-L1 version is uniform inL,Q and applies to bounded nonintegrable scattering phases. The reference counting sawtooth has absolute value at most1/2 on the occupied interval.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V26 Actual meanfield normalization and uniform reference Bethe error

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:384](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L384), `lem:root-limits, reference quantiles`.

**Question:** Are the actual reference quantiles normalized correctly, and is their finite Bethe residual bounded independently of chain length and cutoff?

**Evidence:** The finite-interval density is even by the actual kernel equation and uniqueness. Its actual meanfield primitive equals cumulative minus M_Q/2, including the additive constant. For the constructed reference quantiles the actual finite Bethe residual has sup norm at most h/2, h=norm(K)_1=abs(1-2*lambda/pi), and the actual reference counting-density error from L*r_Q is at most norm(K_prime)_1/2 on the entire line, independently ofL,Q. These estimates are at the reference list; no correction to on-shell roots is inferred.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V27 Exact free-fermion reference normalization

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:338](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L338), `lem:root-limits, reference quantiles`.

**Question:** Are the actual reference quantiles normalized correctly, and is their finite Bethe residual bounded independently of chain length and cutoff?

**Evidence:** At lambda=pi/2, h=0 and the constructed reference list satisfies the exact finite zero-twist consecutive Bethe equations. This checks its phase and cumulative normalization. It does not establish the general-parameter quantitative correction or sector Perron identification.

**Remaining work:** The full Lemma3.1 remains partial. Quantitative correction to on-shell roots, weighted Gaudin/mixed estimates, explicit r evaluation and exponential deficit, lower/positive-K comparisons, nominal edges and sector Perron identification remain open.

### V28 Actual finite-interval relative regularity

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:382](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L382), `lem:root-limits, reference correction`.

**Question:** Are the required weighted estimates proved for the actual reference density and finite Jacobian, and do they give exact roots?

**Evidence:** The actual r_Q derivative is constructed as a bounded continuous convolution expression, with its genuine derivative and L1 properties. For lambda>=pi/2, abs(r_Q_prime)<=C_lambda*r_Q, so log r_Q is uniformly Lipschitz and the density has a two-sided exponential comparison. No explicit hyperbolic formula is assumed.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V29 Actual weighted reference quadrature and kernel rows

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:397](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L397), `lem:root-limits, reference correction`.

**Question:** Are the required weighted estimates proved for the actual reference density and finite Jacobian, and do they give exact roots?

**Evidence:** Applying local reference quadrature to q(u-v)/(L*r_Q(v)) proves its actual quotient derivative and error bound (norm(q_prime)_1+C_lambda*norm(q)_1)/(2*M), where L*r_Q>=M on[-Q,Q]. For the actual negative kernel this yields the absolute reference matrix row bound h+B_lambda/M.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V30 Actual reference Gaudin Jacobian and uniform inverse

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:392](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L392), `lem:root-limits, reference correction`.

**Question:** Are the required weighted estimates proved for the actual reference density and finite Jacobian, and do they give exact roots?

**Evidence:** The actual scaled reference Gaudin Jacobian is exactly I plus the weighted kernel matrix and its actual diagonal counting-density error. That diagonal error has norm at most norm(K_prime)_1/(2*M). A finite-dimensional Neumann series gives both inverse identities and a uniform inverse norm, with the density threshold and norm bound fixed before all finite reference data. For bounded cutoffs the required density threshold follows from r_Q>=s and the actual bare-source tail bound, uniformly for large L.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V31 Actual bounded-cutoff quantile-to-root correction

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:408](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L408), `lem:root-limits, reference correction`.

**Question:** Are the required weighted estimates proved for the actual reference density and finite Jacobian, and do they give exact roots?

**Evidence:** An alternative maximum-principle proof is checked for lambda>=pi/2: the homogeneous counting system reflects coordinatewise order. Uniform translations preserve every interaction difference. The reference residual and a local bare-phase derivative lower bound bracket every exact root within C/L of its reference point when Q is bounded. Using the already proved global root existence gives actual exact ordered roots with a uniformly bounded L*r_Q-weighted displacement. The constants and chain threshold precede all reference data. This bounded-cutoff result does not imply the near-half-filled result with Q tending to infinity.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V32 Actual bounded-cutoff corrected-root density

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:389](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L389), `lem:root-limits, uniform reference correction`.

**Question:** Are root correction and its density estimate proved uniformly in the cutoff for the actual finite equations?

**Evidence:** Actual corrected-root density is L*r_Q+O(1) on the entire real line for boundedQ. The finite reference mass itself forces2n<L. This result uses the already checked C/L physical correction and actual global K-prime Lipschitz bound.

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V33 Actual multiplicative kernel and configuration variation

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:401](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L401), `lem:root-limits, uniform reference correction`.

**Question:** Are root correction and its density estimate proved uniformly in the cutoff for the actual finite equations?

**Evidence:** A genuine derivative bound proves two-sided exponential comparisons for actual s and -K, including the zero kernel at lambda=pi/2. Actual configuration differences give multiplicative counting-density and weighted-kernel-row estimates. Relative kernel increments are bounded by C*exp(C*eps)*abs(K(u))*abs(v-u).

**Remaining work:** The actual negative-K lower comparison and paper boundary-density criterion, strict mass/unique cutoffs and regular-filling root/density conclusion are now checked (V36-V40). The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V34 Uniform density-weighted root bracket and exact correction

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:408](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L408), `lem:root-limits, uniform reference correction`.

**Question:** Are root correction and its density estimate proved uniformly in the cutoff for the actual finite equations?

**Evidence:** For each physical lambda>=pi/2, constants M>0 and radius>0 are fixed before every n,L,Q and actual reference configuration. If L*r_Q>=M throughout[-Q,Q], density-weighted shifts Y_j+t/(L*r_Q(Y_j)) have a positive counting-equation drift on a fixed t-segment. The true derivative is computed from the actual Gaudin matrix. Its lower bound tends to1-h as M grows. The reference residual and the proved homogeneous maximum principle bracket every exact root between the two shifts. Existing global existence supplies actual exact ordered roots with L*r_Q(Y_j)*abs(Z_j-Y_j)<=radius. No bounded-cutoff hypothesis or external correction estimate is used.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V35 Uniform whole-line density error at corrected roots

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:412](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L412), `lem:root-limits, uniform reference correction`.

**Question:** Are root correction and its density estimate proved uniformly in the cutoff for the actual finite equations?

**Evidence:** The relative kernel increment estimate and actual weighted reference row bound transfer that correction to the whole-line density: abs(rho_Z(u)-L*r_Q(u))<=C for all realu, with M,radius,C chosen before every finite datum and cutoff. The threshold is stated in terms of actual L*r_Q; the paper condition using L*r(Q) still needs the lower comparison r_Q>=c*r. No Fourier evaluation or lower comparison is assumed.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V36 Actual full-line radial density without a Fourier formula

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:270](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L270), `lem:root-limits, negative-K construction`.

**Question:** Are the paper lower density comparison and regular/dense-boundary root construction proved for the actual inverse-defined density and finite equations?

**Evidence:** The actual inverse-defined full-line density is radially decreasing for lambda>=pi/2. A pointwise pairing of integration variables v and x+y-v proves preservation of radial decrease by integrable convolution. The property survives the actual norm-convergent Neumann series. The physical s and -K satisfy it by their actual hyperbolic denominators. No Fourier formula is assumed.

**Remaining work:** The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V37 Actual exit-kernel lower density comparison

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:266](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L266), `lem:root-limits, negative-K construction`.

**Question:** Are the paper lower density comparison and regular/dense-boundary root construction proved for the actual inverse-defined density and finite equations?

**Evidence:** For lambda>=pi/2 and Q>=0, the actual exterior-kernel source is exactly the source of r-r_Q. The constant h*r(Q), h=norm(K)_1<1, is a supersolution. Positivity of the actual window inverse gives r(u)-r_Q(u)<=h*r(Q) on the entire line. Consequently (1-h)*r(u)<=r_Q(u)<=r(u) for abs(u)<=Q, and r_Q(u)>=(1-h)*r(Q) there. This proves the paper negative-K lower comparison and verifies the actual minimum-density condition from its L*r(Q) boundary criterion.

**Remaining work:** The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V38 Exact root construction under the paper boundary criterion

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:392](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L392), `lem:root-limits, negative-K construction`.

**Question:** Are the paper lower density comparison and regular/dense-boundary root construction proved for the actual inverse-defined density and finite equations?

**Evidence:** Constants threshold,radius,C are fixed before every n,L,Q. Exact actual mid-quantiles and ordered zero-twist Bethe roots are constructed whenever L*M_Q=n and L*r(Q)>=threshold. Their density-scaled displacement is at most radius and their actual counting-density error from L*r_Q is at most C on the whole line. This applies eventually to every family with L*r(Q)->infinity, including unbounded cutoffs. No true-density threshold is supplied as an external estimate.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V39 Strict filling mass and unique actual cutoffs

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:381](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L381), `lem:root-limits, negative-K construction`.

**Question:** Are the paper lower density comparison and regular/dense-boundary root construction proved for the actual inverse-defined density and finite equations?

**Evidence:** The actual negative-K filling mass is strictly increasing on nonnegative cutoffs; every rho in(0,1/2) has exactly one nonnegative cutoff. Every family of filling masses tending to rho<1/2 has eventually bounded cutoffs. No mass derivative identity is used or assumed.

**Remaining work:** The whole Lemma3.1 remains partial. Still open: explicit full-line r evaluation and the stated exponential mass-defect rate, positive-K density comparison/root construction, nominal edge estimates and sector Perron identification, and remaining limiting quadrature conclusions.

### V40 Actual regular-filling root and density construction

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:408](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L408), `lem:root-limits, negative-K construction`.

**Question:** Are the paper lower density comparison and regular/dense-boundary root construction proved for the actual inverse-defined density and finite equations?

**Evidence:** For a homogeneous negative-K family with L->infinity, L*M_Q=n and n/L->rho<1/2, the selected cutoffs are eventually bounded and L*r(Q)->infinity. Actual reference quantiles and exact ordered roots, the uniform density-scaled displacement and the whole-line L*r_Q+O(1) counting-density estimate then hold eventually. The constants depend only onlambda and are chosen before all families and rho.

**Remaining work:** The actual negative-K occupied window and regular-filling unit bounded-Lipschitz convergence are now checked (V41-V43). The whole named Lemma3.1 remains partial. Open: positive-K comparison/construction and quadrature, explicit r evaluation/exponential mass deficit, nominal edges and Perron identification, array two-stage uniform quadrature, and convergence for arbitrary compact continuous tests beyond the checked bounded-Lipschitz class.

### V41 Actual corrected counting-function primitive error

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:389](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L389), `lem:root-limits, local quadrature`.

**Question:** Is compact-window occupation proved for the actual corrected roots, and does the ordinary root measure then converge in the regular-filling convention?

**Evidence:** The actual theta derivative is K, and the proved multiplicative kernel comparison bounds its increments without assuming theta is L1. Actual density-scaled root displacements and weighted reference rows give a uniform whole-line error for xi_Z from L*cdf_Q-n/2, under the actual reference density threshold. Every input is proved for actual reference quantiles and on-shell roots.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V42 Actual uniform occupied counting windows

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:430](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L430), `lem:root-limits, local quadrature`.

**Question:** Is compact-window occupation proved for the actual corrected roots, and does the ordinary root measure then converge in the regular-filling convention?

**Evidence:** For Q>=A+1, the actual density r_Q>=s gives a positive Q-independent mass on unit bands on both sides of[-A,A]. Thus cdf_Q(u)>=d and M_Q-cdf_Q(u)>=d there. The counting-function error and exact L*M_Q=n then prove -n/2<=xi_Z(u)<=n/2 when L is large. The boundary threshold, chain threshold and margin are fixed before all finite configurations. Occupation is a conclusion, not a supplied assumption.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V43 Regular-filling bounded-Lipschitz quadrature convergence

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:434](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L434), `lem:root-limits, local quadrature`.

**Question:** Is compact-window occupation proved for the actual corrected roots, and does the ordinary root measure then converge in the regular-filling convention?

**Evidence:** For every fixed A>0, one boundary threshold, natural chain threshold and C>0 precede all actual reference and root data. If Q>=A+1 and L*r(Q) exceeds that threshold, the actual root measure has error<=C/L against every unit bounded-Lipschitz test supported on[-A,A]. Hence its integrals converge to Lebesgue integrals along every dense-boundary family whose enlarged support is eventually inside Q. For regular filling n/L->rho<1/2, this applies when M_(A+1)<rho. Since M_(A+1)<1/2, every fixed compact support is covered for fillings sufficiently close to half. No occupation of arbitrary compacts at a fixed sub-half filling is claimed.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V44 Actual bare array counting and c/d bulk density

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:38](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L38), `lem:root-limits, array quadrature`.

**Question:** Are the array density and quadrature estimates uniform in moving bulk centers and in the stated order of width and spacing limits?

**Evidence:** For the actual site array b_j=(j-(L-1)/2)*d/2, the proved finite sawtooth gives count_le(u+1)-count_le(u-1)>=1/d whenever0<d<=1 andabs(u)+1<=L*d/4. Indicator-sum identities and actual positive source-kernel bounds then prove a bare source sum>=c_lambda/d. In the negative-kernel regime the actual counting density exceeds that source sum, uniformly in every root list. No density asymptotic or floor-counting estimate is assumed.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V45 Uniform moving-center array quadrature

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:430](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L430), `lem:root-limits, array quadrature`.

**Question:** Are the array density and quadrature estimates uniform in moving bulk centers and in the stated order of width and spacing limits?

**Evidence:** The actual half-filled array root measure has error<=C_lambda,A*d against every unit bounded-Lipschitz test on[a-A,a+A], whenabs(a)+A+1<=L*d/4. The counting window is proved globally at half filling. Translation of a fixed test follows the moving center and preserves its Lebesgue integral. All constants precede L,d,a,roots and tests.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V46 Actual two-stage array quadrature limit

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:54](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L54), `lem:root-limits, array quadrature`.

**Question:** Are the array density and quadrature estimates uniform in moving bulk centers and in the stated order of width and spacing limits?

**Evidence:** The exact manuscript width B=L*d/2 and bulk constraint abs(a)<=(1-gamma)*B/2 imply the required support condition once B>=2*(A+1)/gamma. For every eps>0 the checked theorem chooses d0,B0 before all0<d<d0,allowed widths,bulk centers,root lists and unit bounded-Lipschitz tests, and proves error<=eps. Thus it certifies the B->infinity then d->0 array quadrature convention with moving centers. It in fact supplies one width threshold independent of small d.

**Remaining work:** The compact continuous test extension is now checked in the strict negative-K regime (V47-V49). Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V47 Proved compact Lipschitz approximation and normalization

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:425](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L425), `lem:root-limits, local Lebesgue convergence`.

**Question:** Does the actual local quadrature convergence extend from Lipschitz tests to arbitrary compact continuous tests with the stated uniformity?

**Evidence:** Every real bounded continuous test supported in[-A,A] has a proved compact Lipschitz approximation supported in[-A-1,A+1], with arbitrarily small uniform error. The proof uses polynomial approximation, a compact derivative bound, a domain clamp and a cutoff. Every bounded Lipschitz approximant is a positive scalar multiple of a unit bounded-Lipschitz test, with the same zero set. No approximation result is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V48 Actual compact continuous quadrature convergence

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:114](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L114), `lem:root-limits, local Lebesgue convergence`.

**Question:** Does the actual local quadrature convergence extend from Lipschitz tests to arbitrary compact continuous tests with the stated uniformity?

**Evidence:** For pi/2<lambda<pi, the actual reciprocal-density root measure has a uniform compact integral approximation bound, using its already proved interval-mass bound. The matching Lebesgue estimate and scalar normalization extend actual unit bounded-Lipschitz convergence to every compact continuous test. This is applied to actual half-filled chains with uniformly bounded inhomogeneities, dense reference families with eventual Q>=A+2, and regular fillings M_(A+2)<rho<1/2. No arbitrary compact occupation is claimed at a fixed lower filling.

**Remaining work:** Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V49 Moving-center array limit for compact continuous tests

**Status:** Checked in Lean within the stated scope. **Priority:** partial third item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:430](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L430), `lem:root-limits, local Lebesgue convergence`.

**Question:** Does the actual local quadrature convergence extend from Lipschitz tests to arbitrary compact continuous tests with the stated uniformity?

**Evidence:** For every fixed compact continuous test, the actual half-filled array measure satisfies the manuscript width-first, spacing-second local Lebesgue limit uniformly over moving centers in a fixed bulk fraction. The proved Lipschitz approximation and mass estimate are translated with the test; constants depend on the test but precede spacing, width, center and roots. The actual width is B=L*d/2. The strict negative-kernel regime is required by the mass bound.

**Remaining work:** Whole Lemma3.1 remains partial. Open: explicit r evaluation and exponential mass-defect rate, positive-K comparison/root construction/quadrature, nominal edges, sector Perron identification and remaining named statements. The free-point compact continuous extension is not asserted by these strict negative-K transfer theorems.

### V50 Actual full-line density tail and boundary comparison

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:89](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L89), `lem:root-limits, homogeneous dense construction`.

**Question:** Can the actual boundary-density criterion be derived from the finite-window mass deficit without assuming a closed form for r?

**Evidence:** The actual inverse-defined density satisfies r=s+(-K)*r. Relative exponential spatial comparison follows by comparing the actual positive source and interaction kernels under their integral. A fixed positive multiple of r(Q) lies in the unit interval to the right of Q. A proved half-line convolution Fubini identity and the actual positive kernel tail-to-value bounds control the remaining convolution tail. Since norm(K)_1<1, this proves c*r(Q)<=integral_(Q,infinity)r<=C*r(Q), uniformly forQ>=0 andpi/2<lambda<pi. The constants precede every cutoff. No Fourier formula is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. Still open:the explicit full-line r evaluation and exact exponential mass-defect rate,positive-K comparison/root construction/quadrature,nominal edge asymptotics,sector Perron identification and remaining named statements.

### V51 Finite-window deficit comparable to the boundary density

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:99](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L99), `lem:root-limits, homogeneous dense construction`.

**Question:** Can the actual boundary-density criterion be derived from the finite-window mass deficit without assuming a closed form for r?

**Evidence:** Evenness of the actual integrable density identifies its exterior mass with twice the right tail. Combining this with the already proved finite-window deficit comparison proves c*r(Q)<=1/2-M_Q<=C*r(Q), uniformly inQ>=0, for the strict negative-K regime. This is a boundary-value comparison;the exact e^(-Q/eta) rate remains unproved.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V52 Actual roots from a diverging missing-root count

**Status:** Checked in Lean within the stated scope. **Priority:** partial second item of Lemma3.1.

**Location:** [sections/03-thermodynamic-kernels.tex:102](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L102), `lem:root-limits, homogeneous dense construction`.

**Question:** Can the actual boundary-density criterion be derived from the finite-window mass deficit without assuming a closed form for r?

**Evidence:** For every actual mass-selected homogeneous family L*M_Q=n with positive chain length and nonnegative cutoff, divergence of L/2-n implies divergence of L*r(Q). The checked actual quantile/root construction therefore gives eventually distinct ordered zero-twist roots,uniform density-scaled quantile displacement and whole-line counting density L*r_Q+O(1). The constants precede all families and cutoffs. The cutoff may diverge;no fixed positive power growth is required by this proved criterion.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V53 Actual Euler Mellin integral and convergence

**Status:** Checked in Lean within the stated scope. **Priority:** partial explicit-density verification.

**Location:** [sections/02-finite-rows.tex:281](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L281), `eq:dressed-density, candidate transform only`.

**Question:** Is the Fourier transform of the displayed hyperbolic candidate evaluated with genuine integrability and the exact manuscript convention?

**Evidence:** The real Mobius map x/(1-x),with its actual Jacobian,transports both complex-valued integral values and genuine integrability from(0,1) to(0,infinity). The principal complex powers in its Jacobian are calculated exactly. Consequently the true Mellin integral of t^(z-1)/(1+t) equals the beta integral B(z,1-z). In0<Re(z)<1 it is absolutely integrable and equals pi/sin(pi*z),by the proved Mathlib beta/gamma reflection formulas. No Mellin identity is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V54 Exact hyperbolic secant Fourier integral

**Status:** Checked in Lean within the stated scope. **Priority:** partial explicit-density verification.

**Location:** [sections/02-finite-rows.tex:281](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L281), `eq:dressed-density, candidate transform only`.

**Question:** Is the Fourier transform of the displayed hyperbolic candidate evaluated with genuine integrability and the exact manuscript convention?

**Evidence:** The exponential substitution and the middle line z=(1-I*a)/2 convert this true Mellin integral into the actual hyperbolic secant Fourier integral. Its absolute integrability and exact unnormalized transform are proved:integral exp(-I*a*x)/(2*cosh(x)) dx=pi/(2*cosh(pi*a/2)). The principal complex logarithm and all frequency/scaling constants are checked.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V55 Displayed density candidate transform and normalization

**Status:** Checked in Lean within the stated scope. **Priority:** partial explicit-density verification.

**Location:** [sections/02-finite-rows.tex:281](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L281), `eq:dressed-density, candidate transform only`.

**Question:** Is the Fourier transform of the displayed hyperbolic candidate evaluated with genuine integrability and the exact manuscript convention?

**Evidence:** Define the displayed candidate profile r_explicit(lambda,u)=1/(2*lambda*cosh(u/(lambda/pi))). For everylambda>0 and every real frequency p,its actual Fourier integrand is integrable and its transform is exactly1/(2*cosh(lambda*p/2)),in the manuscript convention exp(-I*p*u). The displayed real profile is genuinely integrable. This is the candidate transform;it does NOT yet identify r_explicit with the inverse-defined fullLineDensityFunction.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V56 Uniform shifted Mellin bounds and absolute convergence

**Status:** Checked in Lean within the stated scope. **Priority:** partial physical kernel-transform verification.

**Location:** [sections/02-finite-rows.tex:285](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L285), `eq:kernel-transforms,open Mellin strip`.

**Question:** Can the actual shifted and quadratic Mellin integrals be evaluated with convergence and principal branches justified,without assuming the paper kernel transforms?

**Evidence:** For each actual slit-plane shift a,the denominator norm(t+a) has a positive lower bound c*(1+t) on t>=0. The bound is uniform in a neighborhood ofa. The genuine shifted Mellin integrand and its parameter derivative are bounded by fixed multiples of the already proved integrable Euler kernel. This proves actual absolute integrability for0<Re(z)<1 and a inComplex.slitPlane.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V57 Actual holomorphy and slit-plane Mellin evaluation

**Status:** Checked in Lean within the stated scope. **Priority:** partial physical kernel-transform verification.

**Location:** [sections/02-finite-rows.tex:285](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L285), `eq:kernel-transforms,open Mellin strip`.

**Question:** Can the actual shifted and quadratic Mellin integrals be evaluated with convergence and principal branches justified,without assuming the paper kernel transforms?

**Evidence:** Complex differentiation under the actual shifted Mellin integral is justified by that local common majorant. The resulting function is holomorphic on the slit plane. Actual positive real scaling evaluates it on the positive real shifts;analytic uniqueness,using the proved star-convexity of the slit plane and an explicit accumulation set,then proves integral_0^infinity t^(z-1)/(t+a)=a^(z-1)*pi/sin(pi*z) throughout the slit plane and0<Re(z)<1. No shifted integral or holomorphy premise is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V58 Actual physical quadratic Mellin formula

**Status:** Checked in Lean within the stated scope. **Priority:** partial physical kernel-transform verification.

**Location:** [sections/02-finite-rows.tex:285](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L285), `eq:kernel-transforms,open Mellin strip`.

**Question:** Can the actual shifted and quadratic Mellin integrals be evaluated with convergence and principal branches justified,without assuming the paper kernel transforms?

**Evidence:** Partial fractions and the proved shifted formula evaluate the genuine two-pole Mellin integral,with absolute convergence. For the actual conjugate unit-circle factors exp(+-I*alpha),-pi<alpha<pi,the principal logarithms,nonvanishing and distinctness are proved. The normalized physical quadratic integral of[-sin(alpha)/pi]*t^(z-1)/(t^2+2*cos(alpha)*t+1) is exactlysin(alpha*(z-1))/sin(pi*z),for0<Re(z)<1. The alpha=0 free case is included by its identically zero integrand. Actual whole-line dominated convergence also proves that the damped Fourier integral of kernelK is continuous as damping tends tozero. The substitution connecting that integral to the Mellin formula remains separate.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V59 Actual physical source and kernel Fourier transforms

**Status:** Checked in Lean within the stated scope. **Priority:** physical density identification.

**Location:** [sections/02-finite-rows.tex:275](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L275), `eq:kernel-transforms`.

**Question:** Does the actual inverse-defined density satisfy the displayed Fourier and exponential formulas without assuming those analytic identities?

**Evidence:** The actual exponential substitution connects the physical quadratic Mellin integral to the damped kernel Fourier integral, with its exact Jacobian. The already proved dominated limit removes damping. The actual interaction and source transforms now equal the manuscript hyperbolic-sine quotients at every nonzero real frequency. At zero, the proved kernel masses supply the continuous values explicitly. The free point is included. No transform identity is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V60 Actual inverse density equals the explicit hyperbolic profile

**Status:** Checked in Lean within the stated scope. **Priority:** physical density identification.

**Location:** [sections/02-finite-rows.tex:281](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/02-finite-rows.tex#L281), `eq:dressed-density`.

**Question:** Does the actual inverse-defined density satisfy the displayed Fourier and exponential formulas without assuming those analytic identities?

**Evidence:** The actual inverse-defined density equation is complexified and Fourier transformed using proved L1 integrability and the convolution theorem, with exact conversion between angular and Mathlib frequency conventions. Hyperbolic algebra and proved nonvanishing give its actual transform 1/(2*cosh(lambda*p/2)). The displayed profile has the same transform, is continuous and integrable, and its transform is integrable. Fourier inversion proves pointwise fullLineDensityFunction(lambda,u)=1/(2*lambda*cosh(u/(lambda/pi))) for every 0<lambda<pi and every real u.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V61 Exact exponential negative-kernel filling-deficit rate

**Status:** Checked in Lean within the stated scope. **Priority:** physical density identification.

**Location:** [sections/03-thermodynamic-kernels.tex:103](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L103), `lem:root-limits,second item`.

**Question:** Does the actual inverse-defined density satisfy the displayed Fourier and exponential formulas without assuming those analytic identities?

**Evidence:** The identified actual density satisfies exp(-Q/(lambda/pi))/(2*lambda)<=r(Q)<=exp(-Q/(lambda/pi))/lambda for every Q>=0 and every 0<lambda<pi. Combining this with the checked boundary-value deficit comparison proves c*exp(-Q/(lambda/pi))<=1/2-M_Q<=C*exp(-Q/(lambda/pi)) uniformly for Q>=0 in the strict negative-kernel regime pi/2<lambda<pi. The finite-window positive-kernel counterpart remains open.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V62 Actual auxiliary positive kernel

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window comparison clause.

**Location:** [sections/03-thermodynamic-kernels.tex:282](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L282), `lem:root-limits,eq:regular-density-comparison`.

**Question:** Are the actual positive resolvent and all-regime finite-window comparisons proved without assuming positivity of an alternating inverse?

**Evidence:** The actual displayed auxiliary J kernel is a rescaling of the physical bare kernel. Its nonnegativity, absolute integrability, exact mass (pi-2lambda)/(pi-lambda), and actual nonzero-frequency Fourier transform are proved for 0<lambda<pi/2. Frequency zero uses the actual integral, not a literal sinh(0)/sinh(0) quotient.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V63 Actual positive dressed resolvent and its mass

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window comparison clause.

**Location:** [sections/03-thermodynamic-kernels.tex:294](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L294), `lem:root-limits,eq:regular-density-comparison`.

**Question:** Are the actual positive resolvent and all-regime finite-window comparisons proved without assuming positivity of an alternating inverse?

**Evidence:** The constructed physicalResolventKernel equals the actual convolution J*r as a bounded continuous function. The proof transforms its actual integral equation and uses Fourier inversion with proved function and transform integrability. Thus the actual resolvent is nonnegative and its L1 mass is h/(1+h)<1/2 in the positive-K range. No positivity of an alternating finite-window Neumann series is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V64 Uniform finite-window comparison in every physical regime

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window comparison clause.

**Location:** [sections/03-thermodynamic-kernels.tex:325](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L325), `lem:root-limits,eq:regular-density-comparison`.

**Question:** Are the actual positive resolvent and all-regime finite-window comparisons proved without assuming positivity of an alternating inverse?

**Evidence:** Actual Fubini associativity for L1 kernels and a bounded measurable right factor covers the exterior indicator. It proves the exterior-resolvent operator identity and rewrites the existing finite-window inverse as a genuine fixed point. Its operator norm is at most the actual resolvent L1 mass. Positive Neumann comparison and an explicit supersolution prove r<=r_Q<=r/(1-tau) on every window, including endpoints, and 1/(1+h)<=H_Q<=1, for 0<lambda<pi/2. Combined with the checked negative-K and free cases, exists_uniform_finiteInterval_comparison proves constants c,C>0, depending only onlambda and chosen before all Q>=0 and abs(u)<=Q, with c*r<=r_Q<=C*r and c<=H_Q<=C for every 0<lambda<pi.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V65 Actual positive-K strict filling-mass monotonicity

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window filling and rate clauses.

**Location:** [sections/03-thermodynamic-kernels.tex:365](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L365), `lem:root-limits,second item`.

**Question:** Are filling-mass monotonicity,cutoff selection and the exponential deficit proved for the actual inverse-defined functions in every physical parameter regime?

**Evidence:** The actual positive-K finite-window density decreases pointwise with increasing cutoff, as follows from the actual positive exterior operator and fixed-point comparison. Its ordinary exterior integral equals 2*(1-lambda/pi)*(1/2-M_Q). Comparing those integrals across cutoffs, with a strictly positive lost band, proves strict filling-mass monotonicity on Q>=0. No endpoint-derivative formula is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V66 Actual filling cutoffs throughout the physical range

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window filling and rate clauses.

**Location:** [sections/03-thermodynamic-kernels.tex:101](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L101), `lem:root-limits,second item`.

**Question:** Are filling-mass monotonicity,cutoff selection and the exponential deficit proved for the actual inverse-defined functions in every physical parameter regime?

**Evidence:** Combining the two signs of K and the free point, the actual M_Q is strictly increasing on Q>=0, M_0=0, 0<M_Q<1/2 for every finite Q>0, and M_Q tends to1/2. Every prescribed filling rho in(0,1/2) has exactly one actual nonnegative cutoff; every family of masses converging strictly below one half has eventually bounded cutoffs. All statements hold for every 0<lambda<pi.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V67 Exact all-physical exponential filling deficit

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window filling and rate clauses.

**Location:** [sections/03-thermodynamic-kernels.tex:104](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L104), `lem:root-limits,second item`.

**Question:** Are filling-mass monotonicity,cutoff selection and the exponential deficit proved for the actual inverse-defined functions in every physical parameter regime?

**Evidence:** The actual full-line exterior mass is between exp(-Q/(lambda/pi))/pi and twice that expression for Q>=0, by the identified density, evenness and actual exponential integration. The ordinary finite-window deficit is comparable to that exterior mass in both parameter regimes. Consequently the exact manuscript rate c*exp(-Q/(lambda/pi))<=1/2-M_Q<=C*exp(-Q/(lambda/pi)) is proved for every 0<lambda<pi, with positive constants chosen before every cutoff, including the free point.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V68 Actual full-line spatial comparison

**Status:** Checked in Lean within the stated scope. **Priority:** finite-window filling and rate clauses.

**Location:** [sections/03-thermodynamic-kernels.tex:353](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L353), `lem:root-limits,second item`.

**Question:** Are filling-mass monotonicity,cutoff selection and the exponential deficit proved for the actual inverse-defined functions in every physical parameter regime?

**Evidence:** The actual identified full-line density satisfies a two-sided spatial exponential comparison with exact inverse length pi/lambda, throughout the physical range. The proof compares the two exponentials defining cosh and then uses the proved actual density identification.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V69 Actual all-physical relative density regularity

**Status:** Checked in Lean within the stated scope. **Priority:** actual reference construction and Jacobian estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:350](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L350), `lem:root-limits,reference stage`.

**Question:** Are the actual reference quantiles,quadrature,derivative and Gaudin inverse estimates proved for every physical lambda before the on-shell nonlinear perturbation step?

**Evidence:** The actual positive dressed resolvent and finite-window density inherit the exact full-line spatial comparison by positive convolution. Taking logarithms and applying the derivative bound for a Lipschitz function proves the actual positive-K relative derivative estimate. Together with the negative-K result, one cutoff-independent physicalDensityLogConstant=kernelLogConstant+pi/lambda controls the actual density derivative,log variation and spatial comparison throughout 0<lambda<pi.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V70 Actual all-physical reference quantiles and residuals

**Status:** Checked in Lean within the stated scope. **Priority:** actual reference construction and Jacobian estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:385](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L385), `lem:root-limits,reference stage`.

**Question:** Are the actual reference quantiles,quadrature,derivative and Gaudin inverse estimates proved for every physical lambda before the on-shell nonlinear perturbation step?

**Evidence:** Actual finite-window positivity and the ordinary cumulative integral give unique interior quantiles,strictly ordered mid-quantiles and mass-selected ReferenceQuantileData for every physical lambda and every finite strictly subhalf filling. The local counting sawtooth and unweighted quadrature are checked for those actual data. Their actual Bethe counting residual and density error are uniformly bounded. These are continuum reference configurations,not on-shell roots.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V71 Actual all-physical weighted reference quadrature

**Status:** Checked in Lean within the stated scope. **Priority:** actual reference construction and Jacobian estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:393](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L393), `lem:root-limits,reference stage`.

**Question:** Are the actual reference quantiles,quadrature,derivative and Gaudin inverse estimates proved for every physical lambda before the on-shell nonlinear perturbation step?

**Evidence:** The actual weighted reference quotient is differentiated with its genuine density-derivative term. The proved all-physical relative bound supplies an L1 majorant. Ordinary counting quadrature gives a weighted kernel error of order1/M. Constant sign of the physical kernel then yields the actual absolute weighted-row and operator-norm bounds for both signs,including the zero free-point kernel.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V72 Actual reference Gaudin inverses and thresholds

**Status:** Checked in Lean within the stated scope. **Priority:** actual reference construction and Jacobian estimates.

**Location:** [sections/03-thermodynamic-kernels.tex:401](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L401), `lem:root-limits,reference stage`.

**Question:** Are the actual reference quantiles,quadrature,derivative and Gaudin inverse estimates proved for every physical lambda before the on-shell nonlinear perturbation step?

**Evidence:** The original scaled reference Gaudin operator equals identity plus the actual kernel row operator and actual diagonal density error. The proved all-physical bounds give a uniform convergent Neumann inverse once the actual scaled density exceeds a fixed threshold. Both inverse identities and the norm bound are checked. Uniform finite-window comparison supplies that threshold on bounded cutoffs as chain length grows,and under one full-line boundary criterion L*r(Q)>=D even for unbounded cutoffs. The actual reference Gaudin matrix is nonsingular at sufficiently dense bounded-cutoff reference data. This does not yet prove positive-K on-shell root construction or stability of the Jacobian under nonlinear perturbation.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V73 Actual all-physical nonlinear Jacobian perturbation

**Status:** Checked in Lean within the stated scope. **Priority:** actual nonlinear root construction.

**Location:** [sections/03-thermodynamic-kernels.tex:401](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L401), `lem:root-limits,nonlinear root stage`.

**Question:** Are the actual finite equations solved near the actual quantiles for both kernel signs,with proved ordering and uniform density control?

**Evidence:** Actual absolute-kernel and density-profile translation estimates cover both physical kernel signs and the free point. Weighted configuration displacements control the actual counting-density error globally. The diagonal and interaction-row estimates combine into a bound for the original scaled nonlinear Gaudin operator relative to the actual reference operator. Its explicit error tends to zero as the scaled-density threshold grows,with constants fixed before every root count,chain length and cutoff.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V74 Quantitative Newton for the actual finite equations

**Status:** Checked in Lean within the stated scope. **Priority:** actual nonlinear root construction.

**Location:** [sections/03-thermodynamic-kernels.tex:412](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L412), `lem:root-limits,nonlinear root stage`.

**Question:** Are the actual finite equations solved near the actual quantiles for both kernel signs,with proved ordering and uniform density control?

**Evidence:** A checked quantitative local-surjectivity criterion is applied to the actual finite Bethe counting map in the reference density coordinates. The actual residual and actual derivative estimates satisfy its hypotheses. This constructs exact finite solutions near the actual continuum mid-quantiles throughout 0<lambda<pi; no positive-K global order-reflection assumption is used.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V75 Actual ordered roots and density under the boundary criterion

**Status:** Checked in Lean within the stated scope. **Priority:** actual nonlinear root construction.

**Location:** [sections/03-thermodynamic-kernels.tex:426](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L426), `lem:root-limits,nonlinear root stage`.

**Question:** Are the actual finite equations solved near the actual quantiles for both kernel signs,with proved ordering and uniform density control?

**Evidence:** The actual continuum profile has an exponential lower bound on the expanded occupied window. For a sufficiently large fixed scaled-density threshold,the actual perturbed counting derivative is positive there. Consecutive target levels therefore force strict ordering of the constructed solutions. The actual roots obey a uniform weighted quantile bound and an O(1) counting-density error on the entire real line. Uniform finite-window comparison translates the threshold into the manuscript boundary criterion L*r(Q)>=D,even when Q diverges. Every constant precedes the finite data.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V76 Actual all-physical Gaudin nonsingularity and twist branches

**Status:** Checked in Lean within the stated scope. **Priority:** actual regular root families and branches.

**Location:** [sections/03-thermodynamic-kernels.tex:433](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L433), `lem:root-limits,root families and branches`.

**Question:** Are the actual homogeneous root families,endpoint extensions and analytic branches proved throughout the physical parameter range?

**Evidence:** A convergent Neumann correction of the actual reference right inverse proves nonsingularity of the original actual Gaudin matrix throughout a sufficiently small weighted configuration neighborhood. The actual ordered roots and uniform density error are assembled with this nonsingularity for every physical lambda. Under the manuscript boundary-density criterion,these actual roots have real-analytic twist branches and the exact Gaudin response identity at every sufficiently nearby twist. No determinant premise or inverse is assumed for the constructed roots.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V77 Actual whole-line counting error and endpoint extensions

**Status:** Checked in Lean within the stated scope. **Priority:** actual regular root families and branches.

**Location:** [sections/03-thermodynamic-kernels.tex:421](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L421), `lem:root-limits,root families and branches`.

**Question:** Are the actual homogeneous root families,endpoint extensions and analytic branches proved throughout the physical parameter range?

**Evidence:** The actual scattering phase derivative and absolute-kernel comparison prove relative phase increments for both kernel signs. Actual weighted root closeness then gives a whole-line counting-phase displacement bound. Combined with actual reference quadrature,this proves uniform discrepancy from the actual finite-window cumulative density,including bounded counting extensions at both endpoints. A single actual-root assembler supplies ordered roots,weighted displacement,whole-line density and primitive errors,and the actual nonsingular Gaudin matrix with all constants chosen before the finite data.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V78 Actual regular-filling and positive-power root families

**Status:** Checked in Lean within the stated scope. **Priority:** actual regular root families and branches.

**Location:** [sections/03-thermodynamic-kernels.tex:426](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L426), `lem:root-limits,root families and branches`.

**Question:** Are the actual homogeneous root families,endpoint extensions and analytic branches proved throughout the physical parameter range?

**Evidence:** Actual finite mass data construct their own reference mid-quantiles and nonsingular ordered roots. Every family whose boundary density times chain length diverges has eventual actual roots with uniform weighted displacement and counting-density error. The bounded-cutoff alternative is uniform over all sufficiently large chains. The explicit c*L^a boundary lower bound with c,a positive implies the dense-boundary criterion. At every limiting filling below half,actual cutoff boundedness is derived from the finite-window mass limit,and the resulting n/L family has eventual roots. These results cover every physical lambda and use the actual manuscript density and finite equations.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V79 Actual atom weights and uniform local mass

**Status:** Checked in Lean within the stated scope. **Priority:** actual inverse-density measure.

**Location:** [sections/03-thermodynamic-kernels.tex:426](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L426), `lem:root-limits,measure and quadrature`.

**Question:** Are actual inverse-density atom weights,mass and local bounded-Lipschitz quadrature proved for both physical kernel signs without assuming a substitute measure?

**Evidence:** Actual reference inverse-density atoms have uniform mass on every fixed-length moving interval,using actual quantile levels and global relative profile comparison. At displaced configurations,the actual counting density differs from its own reference weight by a uniform additive bound. A single fixed density threshold makes all actual atom weights positive,bounds them by twice the reference inverse weights,and bounds their difference by C/w_j^2. The existing actual rootQuadratureMeasure is preserved. Exact actual-measure integration and interval formulas are proved from the genuine weight signs. Uniform unit-interval mass for that actual measure follows throughout the physical range,including moving sparse-edge intervals.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V80 Genuine reference bounded-Lipschitz quadrature

**Status:** Checked in Lean within the stated scope. **Priority:** actual inverse-density measure.

**Location:** [sections/03-thermodynamic-kernels.tex:430](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L430), `lem:root-limits,measure and quadrature`.

**Question:** Are actual inverse-density atom weights,mass and local bounded-Lipschitz quadrature proved for both physical kernel signs without assuming a substitute measure?

**Evidence:** The ordinary actual cumulative density has a bounded continuous representative because its derivative is genuinely L1. Absolute-continuity integration by parts and the actual reference sawtooth give quadrature for compact Lipschitz tests,without replacing them by C1 tests. Dividing by the actual positive reference density and using its proved relative derivative gives weighted bounded-Lipschitz quadrature at the local density scale.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V81 Actual-measure transport,quadrature and local convergence

**Status:** Checked in Lean within the stated scope. **Priority:** actual inverse-density measure.

**Location:** [sections/03-thermodynamic-kernels.tex:432](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L432), `lem:root-limits,measure and quadrature`.

**Question:** Are actual inverse-density atom weights,mass and local bounded-Lipschitz quadrature proved for both physical kernel signs without assuming a substitute measure?

**Evidence:** A genuine transport estimate compares the actual inverse-counting-density measure with the reference weighted atoms. It retains the individual root weights and an arbitrary positive fixed enlargement of the support,so its rate uses the local rather than the global density scale. Combining reference quadrature and transport proves C/N times(Lip(phi)+norm(phi)) for tests supported inside the reference occupied interval. The local scale can be the actual counting density once N exceeds a fixed finite threshold. The corresponding filtered local convergence to Lebesgue measure is checked for varying finite root counts under the proved weighted-neighborhood and density hypotheses.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### U09 Quadrature regions must be occupied

**Status:** Proof located; independent verification remains open. **Priority:** scope clarification.

**Location:** [sections/03-thermodynamic-kernels.tex:120](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L120), `lem:root-limits;eq:local-quadrature`.

**Question:** Does the dense-region quadrature claim explicitly restrict the test region to the occupied root interval?

**Evidence:** The quadrature statement at source lines120-127 does not explicitly repeat that the test region must be occupied. The proof at lines426-438 integrates counting cells,and the preceding density comparison is stated on the occupied interval. The formal theorem makes -Q<=a and a+ell<=Q explicit. A positive or large counting derivative alone outside the occupied root interval does not guarantee Lebesgue quadrature there. This is recorded as an intended-scope clarification,not a confirmed mathematical error.

**Remaining work:** The joint analytic construction is now checked with compact test support inside the occupied reference interval. Confirm this intended scope of dense portions;do not infer quadrature outside it from counting-density positivity alone. If restricted interval tests may be nonzero at endpoints,formulate and prove the boundary terms explicitly.

### V82 Actual quadrature at every positive local density scale

**Status:** Checked in Lean within the stated scope. **Priority:** joint actual root-measure construction.

**Location:** [sections/03-thermodynamic-kernels.tex:430](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L430), `lem:root-limits,joint analytic construction`.

**Question:** Do the same actual selected roots simultaneously satisfy the equations,measure estimates and local convergence for every fixed compact test window?

**Evidence:** Actual inverse-density measure mass is uniformly bounded on every prescribed fixed-length moving interval. A compact-test bound from that actual interval mass controls the finite low-density range. Combining it with the previously proved large-density estimate removes the finite lower cutoff:the actual-measure bounded-Lipschitz error is C/N times(Lip(phi)+norm(phi)) for every N>0,with actual local counting density and explicit occupied-reference-window support.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V83 Joint actual roots,measures and analytic branches

**Status:** Checked in Lean within the stated scope. **Priority:** joint actual root-measure construction.

**Location:** [sections/03-thermodynamic-kernels.tex:426](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L426), `lem:root-limits,joint analytic construction`.

**Question:** Do the same actual selected roots simultaneously satisfy the equations,measure estimates and local convergence for every fixed compact test window?

**Evidence:** PhysicalRootMeasureData records genuine properties of one actual root list:ConsecutiveRoots,weighted quantile displacement,whole-line density error,original Gaudin determinant nonzero,positive actual atom weights,uniform actual unit-interval mass,a real-analytic twist branch with exact Gaudin response,and the all-positive-N actual quadrature bound. Its witnesses are constructed from the previously proved actual root,inverse and measure estimates;none of its fields is introduced as an external assumption. A single larger fixed density threshold guarantees all fields for the same X. The manuscript boundary-density criterion and actual finite mass data then construct the reference quantiles and this same actual X.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V84 Actual root families selected before all test windows

**Status:** Checked in Lean within the stated scope. **Priority:** joint actual root-measure construction.

**Location:** [sections/03-thermodynamic-kernels.tex:126](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L126), `lem:root-limits,joint analytic construction`.

**Question:** Do the same actual selected roots simultaneously satisfy the equations,measure estimates and local convergence for every fixed compact test window?

**Evidence:** The joint construction gives actual root-measure families under the dense-boundary criterion. A stronger selection theorem chooses the reference and actual roots once,before every test-window length and enlargement. For every fixed length and positive enlargement,uniform eventual measure,quadrature and analytic-branch conclusions hold for those same chosen roots. The corresponding filtered local convergence to Lebesgue measure is proved for their actual atomic measures,with varying finite root counts. The earlier regular-filling and positive-power boundary criteria supply the density hypothesis.

**Remaining work:** Whole Lemma3.1 remains partial. The homogeneous analytic root-and-measure block is now assembled throughout the physical range,including all positive local density scales,actual family selection before the test windows,and local convergence. Remaining:sector Perron-vector identification;clarify the occupied-region and compact-support interpretation(U09). If the manuscript intends tests restricted to a closed interval with nonzero endpoint values,explicit boundary terms still need a separate formulation. No claim for nonoccupied regions is made.

### V85 Actual local link derivative and negative hopping

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron-operator prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:442](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L442), `lem:root-limits,Perron argument`.

**Question:** Actual local link derivative and negative hopping for the existing physical matrices?

**Evidence:** The actual complex derivative of physicalR at zero is proved. Multiplication by the swap and negative real scale gives the explicit local six-matrix,opposite-spin hopping -eta/sin(lambda),strict negativity throughout 0<lambda<pi for eta>0,and Hermiticity.

**Remaining work:** Whole Lemma3.1 remains partial. The actual local operator,row derivative,insertion formula,seam link and transfer-row commutation are proved. Still required:identify every insertion with its corresponding nearest-neighbor link;sector graph connectivity and simple positive minimum;free-fermion ground state;continuation of the actual Bethe branch;transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support scope clarification. The homogeneous root-and-measure block remains checked in its explicit occupied compact-test scope.

### V86 Actual homogeneous row derivative and inverse translation

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron-operator prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:442](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L442), `lem:root-limits,Perron argument`.

**Question:** Actual homogeneous row derivative and inverse translation for the existing physical matrices?

**Evidence:** The product rule is proved for the existing ordered finite row contraction and its marked auxiliary trace. It gives the genuine derivative of the actual homogeneous transfer row at the swap,whose value is the cyclic translation. The actual logarithmic Hamiltonian uses the explicit inverse translation. Its entries agree with the scalar derivatives of the actual row entries.

**Remaining work:** Whole Lemma3.1 remains partial. The actual local operator,row derivative,insertion formula,seam link and transfer-row commutation are proved. Still required:identify every insertion with its corresponding nearest-neighbor link;sector graph connectivity and simple positive minimum;free-fermion ground state;continuation of the actual Bethe branch;transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support scope clarification. The homogeneous root-and-measure block remains checked in its explicit occupied compact-test scope.

### V87 Actual logarithmic Hamiltonian commutes with every transfer row

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron-operator prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:462](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L462), `lem:root-limits,Perron argument`.

**Question:** Actual logarithmic Hamiltonian commutes with every transfer row for the existing physical matrices?

**Evidence:** Actual homogeneous physical rows commute at every complex spectral coordinate. Differentiating their entrywise finite product sums proves that the actual row derivative commutes with every row. The explicit inverse translation also commutes with every row,hence so does the actual logarithmic Hamiltonian. No Perron or local-sum identity is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The actual local operator,row derivative,insertion formula,seam link and transfer-row commutation are proved. Still required:identify every insertion with its corresponding nearest-neighbor link;sector graph connectivity and simple positive minimum;free-fermion ground state;continuation of the actual Bethe branch;transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support scope clarification. The homogeneous root-and-measure block remains checked in its explicit occupied compact-test scope.

### V88 Exact single-site insertion expansion and periodic seam link

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron-operator prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:442](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L442), `lem:root-limits,Perron argument`.

**Question:** Exact single-site insertion expansion and periodic seam link for the existing physical matrices?

**Evidence:** The genuine ordered row derivative equals the finite sum of single-site tile insertions,retaining both auxiliary boundary spins and site order. Auxiliary tracing and inverse translation preserve this formula. The first insertion is contracted exactly:it acts on the last and first physical spins and fixes every intervening spin. For the actual R derivative it is exactly the local physical link operator on that periodic seam.

**Remaining work:** Whole Lemma3.1 remains partial. The actual local operator,row derivative,insertion formula,seam link and transfer-row commutation are proved. Still required:identify every insertion with its corresponding nearest-neighbor link;sector graph connectivity and simple positive minimum;free-fermion ground state;continuation of the actual Bethe branch;transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support scope clarification. The homogeneous root-and-measure block remains checked in its explicit occupied compact-test scope.

### V89 Full actual cyclic-link Hamiltonian identity

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:442](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L442), `lem:root-limits,Perron argument`.

**Question:** Full actual cyclic-link Hamiltonian identity with the actual row operators?

**Evidence:** Splitting the existing row contraction at its final site proves invariance of the auxiliary trace under simultaneous cyclic rotation of the physical spins and tile list. Actual translation conjugation moves every interior insertion to the preceding site. Iteration identifies every insertion as a translated first insertion. The genuine logarithmic row derivative therefore equals the full cyclic sum of the explicit last-first physical link operator.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V90 Hermiticity of the actual full Hamiltonian

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:444](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L444), `lem:root-limits,Perron argument`.

**Question:** Hermiticity of the actual full Hamiltonian with the actual row operators?

**Evidence:** The explicit seam matrix is proved Hermitian. Its unitary translation conjugates remain Hermitian,so the actual full logarithmic Hamiltonian is Hermitian. This uses the actual previously defined row derivative and translation,with no assumed Hamiltonian identity.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V91 Constructive adjacent-swap sector connectivity

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:446](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L446), `lem:root-limits,Perron argument`.

**Question:** Constructive adjacent-swap sector connectivity with the actual row operators?

**Evidence:** AdjacentSpinSwap is the concrete nearest-neighbor exchange of opposite binary spins at an arbitrary adjacent pair. Such exchanges preserve minusCount. A constructive proof moves an occupied spin to the front and proves that every two RowSpins configurations with the same particle number are joined by a finite sequence of these exchanges. This establishes combinatorial sector connectivity. Identifying every such exchange with a strictly negative entry of the actual full Hamiltonian remains a separate obligation.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V92 Reality and nonpositive hopping of the actual Hamiltonian

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:445](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L445), `lem:root-limits,Perron argument`.

**Question:** Reality and nonpositive hopping of the actual Hamiltonian with the actual row operators?

**Evidence:** The physical local link and explicit seam have real entries and nonpositive off-diagonal entries for 0<lambda<pi and eta>=0. Powers of actual permutation matrices are proved to rotate both matrix configurations exactly. The cyclic-sum identity then proves that the actual full logarithmic Hamiltonian has real entries and nonpositive off-diagonal entries.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V93 Actual particle-sector preservation and strict first-pair hopping

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:446](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L446), `lem:root-limits,Perron argument`.

**Question:** Actual particle-sector preservation and strict first-pair hopping with the actual row operators?

**Evidence:** The actual translation preserves minusCount,as do all its iterates. The seam link vanishes between different particle counts;hence so does the actual full Hamiltonian. It maps every previously defined SpinSector into itself. For eta>0 an opposite-spin exchange at the first two sites has a strictly negative entry in the actual full Hamiltonian:one explicit translated bond is negative and the remaining off-diagonal terms cannot cancel it.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V94 Connectivity of the actual Hamiltonian hopping graph

**Status:** Checked in Lean within the stated scope. **Priority:** actual Perron Hamiltonian prerequisites.

**Location:** [sections/03-thermodynamic-kernels.tex:446](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L446), `lem:root-limits,Perron argument`.

**Question:** Connectivity of the actual Hamiltonian hopping graph with the actual row operators?

**Evidence:** Cyclic invariance of the actual Hamiltonian transfers the strict first-pair hopping sign to every adjacent pair. The proof keeps the swap position,decreases it by rotating a leading spin to the end,and applies induction. The graph is then defined by distinct vertices in one exact particle sector and strict negativity of the actual full Hamiltonian entry. Its symmetry follows from actual Hermiticity,and its preconnectedness follows by lifting the proved adjacent-swap paths. No graph-connectivity or strict-hopping assumption is introduced.

**Remaining work:** Whole Lemma3.1 remains partial. The full actual nearest-neighbor Hamiltonian identity,Hermiticity,reality,nonpositive off-diagonal entries and particle-sector preservation are proved. The adjacent-swap configuration graph is connected in each sector,and first-pair swaps have strictly negative actual Hamiltonian entries. Every adjacent-swap edge now has a strictly negative actual entry,and the graph defined directly by those actual entries is proved preconnected in each particle sector. Still required:prove the simple positive sector minimum;identify the free-fermion ground state;justify continuation of the actual Bethe branch;prove transfer primitivity and Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V95 Strict positivity and eigenspace simplicity

**Status:** Checked in Lean within the stated scope. **Priority:** actual positive simple sector minimum.

**Location:** [sections/03-thermodynamic-kernels.tex:447](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L447), `lem:root-limits,Perron argument`.

**Question:** Under the stated sign and connectivity hypotheses,does a nonzero nonnegative eigenvector become strictly positive,and does a positive eigenvector span its real eigenspace?

**Evidence:** For a finite real matrix with nonpositive off-diagonals,a zero of a nonnegative eigenvector propagates across every strict negative entry. A preconnected strict-negative-entry graph therefore makes every nonzero nonnegative eigenvector strictly positive. A positive eigenvector spans the entire real eigenspace at its eigenvalue:subtract any other eigenvector from a maximal scalar multiple of the positive one,and use the resulting nonnegative eigenvector with a zero coordinate.

**Remaining work:** Whole Lemma3.1 remains partial. The actual full Hamiltonian,connected sector hopping graph,and strictly positive simple sector minimum are now proved,including the lower energy bound and the entire complex eigenspace. Remaining Perron identification:identify the consecutive-root Bethe vector with this minimum at lambda=pi/2;justify continuation of the actual Bethe branch;prove the needed transfer positivity/primitivity and its Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V96 Exact absolute-value norm and energy control

**Status:** Checked in Lean within the stated scope. **Priority:** actual positive simple sector minimum.

**Location:** [sections/03-thermodynamic-kernels.tex:447](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L447), `lem:root-limits,Perron argument`.

**Question:** Do coordinatewise absolute values preserve the Euclidean norm and lower the actual finite matrix energy under the off-diagonal sign hypothesis?

**Evidence:** The actual finite quadratic matrix energy decreases under coordinatewise absolute values,while the Euclidean norm is preserved exactly. The finite energy equals the inner-product energy of the actual matrix operator on Euclidean space. The diagonal energy terms are treated exactly;only off-diagonal terms use the sign hypothesis.

**Remaining work:** Whole Lemma3.1 remains partial. The actual full Hamiltonian,connected sector hopping graph,and strictly positive simple sector minimum are now proved,including the lower energy bound and the entire complex eigenspace. Remaining Perron identification:identify the consecutive-root Bethe vector with this minimum at lambda=pi/2;justify continuation of the actual Bethe branch;prove the needed transfer positivity/primitivity and its Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V97 Finite positive simple ground-state existence and energy bound

**Status:** Checked in Lean within the stated scope. **Priority:** actual positive simple sector minimum.

**Location:** [sections/03-thermodynamic-kernels.tex:447](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L447), `lem:root-limits,Perron argument`.

**Question:** Finite positive simple ground-state existence and energy bound without assuming an eigenvector or its Perron property?

**Evidence:** A minimum of the actual self-adjoint matrix energy is attained on a compact nonzero sphere. Its absolute-value vector is another minimum. The proved sphere-minimum theorem gives an actual eigenvector;the new positivity and eigenspace lemmas make it strictly positive and simple. An explicit Rayleigh lower bound certifies that its eigenvalue mu is the ground-state minimum:mu times the squared Euclidean norm is at most the energy of every real vector. Eigenvector existence,positivity,simplicity and minimality are all proved,not assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The actual full Hamiltonian,connected sector hopping graph,and strictly positive simple sector minimum are now proved,including the lower energy bound and the entire complex eigenspace. Remaining Perron identification:identify the consecutive-root Bethe vector with this minimum at lambda=pi/2;justify continuation of the actual Bethe branch;prove the needed transfer positivity/primitivity and its Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V98 Positive simple minimum in the actual real particle sectors

**Status:** Checked in Lean within the stated scope. **Priority:** actual positive simple sector minimum.

**Location:** [sections/03-thermodynamic-kernels.tex:447](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L447), `lem:root-limits,Perron argument`.

**Question:** Positive simple minimum in the actual real particle sectors without assuming an eigenvector or its Perron property?

**Evidence:** Every allowed particle count has a concrete RowSpins configuration. The exact real restriction of the actual logarithmic Hamiltonian is Hermitian. Applying the proved finite minimum theorem to this restriction and the actual strict-negative-entry hopping graph gives a strictly positive simple minimum in every valid particle sector,for every 0<lambda<pi and eta>0. The lower energy bound holds for every real vector in that sector.

**Remaining work:** Whole Lemma3.1 remains partial. The actual full Hamiltonian,connected sector hopping graph,and strictly positive simple sector minimum are now proved,including the lower energy bound and the entire complex eigenspace. Remaining Perron identification:identify the consecutive-root Bethe vector with this minimum at lambda=pi/2;justify continuation of the actual Bethe branch;prove the needed transfer positivity/primitivity and its Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V99 Positive simple minimum in the actual complex particle sectors

**Status:** Checked in Lean within the stated scope. **Priority:** actual positive simple sector minimum.

**Location:** [sections/03-thermodynamic-kernels.tex:447](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L447), `lem:root-limits,Perron argument`.

**Question:** Positive simple minimum in the actual complex particle sectors without assuming an eigenvector or its Perron property?

**Evidence:** The exact complex sector restriction equals the scalar embedding of the proved real matrix. Real eigenvectors embed exactly,and splitting a complex eigenvector into real and imaginary parts proves that the entire complex eigenspace at the minimum is one-dimensional. The exact complex Hermitian quadratic energy splits into the two real coordinate energies. The real lower bound therefore gives the full complex lower energy bound with sum of squared complex norms. The actual complex sector Hamiltonian has a positive real ground vector and a simple complex ground eigenspace.

**Remaining work:** Whole Lemma3.1 remains partial. The actual full Hamiltonian,connected sector hopping graph,and strictly positive simple sector minimum are now proved,including the lower energy bound and the entire complex eigenspace. Remaining Perron identification:identify the consecutive-root Bethe vector with this minimum at lambda=pi/2;justify continuation of the actual Bethe branch;prove the needed transfer positivity/primitivity and its Perron identification. U09 remains the occupied-region and compact-support clarification. The earlier analytic root-and-measure block remains checked with its explicit occupied compact-test conditions.

### V100 Common Hamiltonian ground and transfer eigenline

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** The exact restricted Hamiltonian commutes with every actual homogeneous physical transfer row. The constructed strictly positive Hamiltonian ground vector is chosen once before all complex spectral parameters and is an eigenvector of all those transfer rows.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V101 Actual nonnegative transfer row and positive diagonal

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** At spectral parameter lambda/2 the exact physical R tile has equal positive weights d=sin(lambda/2)/sin(lambda). Finite contraction proves that every row entry is real and nonnegative and every diagonal is exactly 2*d^L>0. The actual transfer row preserves every particle sector.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V102 Positive transfer hopping and connected sectors

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** The actual transfer entry for a first-pair particle-hole swap is exactly d^(L-2)>0. Actual cyclic translation invariance transports this to every adjacent hop. The positive-entry graph on each particle sector is preconnected by the already proved configuration paths.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V103 Actual transfer primitivity

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** Every finite graph walk yields a positive entry of the matching matrix power. Positive diagonals extend these to one common positive power. Applying this proved construction to the actual sector transfer matrix gives an explicitly constructed exponent N>0 for which all entries have positive real parts.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V104 Positive Perron root and bounds for all complex eigenvalues

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** For a nonnegative real matrix with positive diagonal and a supplied positive eigenvector, its eigenvalue is real and strictly positive. The weighted maximum-coordinate estimate proves the modulus bound for every complex eigenvalue. Connected positive entries give real eigenspace simplicity; the proved complexification argument gives simplicity of the entire complex eigenspace.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V105 Canonical actual sector Perron certificate

**Status:** Checked in Lean within the stated scope. **Priority:** actual canonical sector Perron data.

**Location:** [sections/03-thermodynamic-kernels.tex:459](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L459), `lem:root-limits,Perron argument`.

**Question:** Is this step proved for the actual finite transfer matrix,with its needed hypotheses explicit?

**Evidence:** PhysicalSectorPerronData is constructed for every 0<lambda<pi,eta>0 and valid particle sector. It includes the actual Hamiltonian lower energy bound and ground eigenvector, a strictly positive transfer eigenvalue, the bound for every complex eigenvalue, the whole simple complex eigenspace and actual transfer primitivity. The canonical vector is constructed by the earlier ground-state existence theorem; no Perron input is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The constructed actual positive Hamiltonian minimum is now the actual physical transfer Perron line,with positive eigenvalue,bounds for every complex eigenvalue,simple entire complex eigenspace and a proved strictly positive transfer power. It is a common eigenline for all complex spectral parameters. Still identify the consecutive-root Bethe vector with this minimum at lambda=pi/2 and justify continuation in lambda. U09 retains the occupied compact-test scope clarification. No Bethe Perron conclusion is claimed.

### V106 Exact physical free-point momentum and dispersion

**Status:** Checked in Lean within the stated scope. **Priority:** actual free-point Slater construction.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Are the exact phase,operator or determinant identities proved with the required boundary and domain conditions explicit?

**Evidence:** The physical shift phase equals -F_i_lambda(y-i*lambda/2),with real branch p=-2*pi*S_lambda(y). At the free point p=-2*arctan(tanh y),cos(p)=1/cosh(2y),and the actual kernel energy -2*pi*(1/2)*s(y) equals -cos(p). The actual homogeneous consecutive-root equations give p_j=pi*(n-1-2j)/L,the fermionic circle sign (-1)^(n-1),exact centering,and strict central-half-circle bounds when 2n<=L. The sign reverses rapidity order.

**Remaining work:** Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

### V107 Finite Slater determinant eigenvalue theorem

**Status:** Checked in Lean within the stated scope. **Priority:** actual free-point Slater construction.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Are the exact phase,operator or determinant identities proved with the required boundary and domain conditions explicit?

**Evidence:** An exact determinant identity sums weighted single-row updates to the sum of orbital weights times the determinant. A Slater determinant vanishes whenever two coordinates collide. If supplied one-particle orbitals obey explicit finite matrix eigenvalue equations,the coordinate Hamiltonian acts on their determinant by the sum of those eigenvalues. These are proved algebraic consequences;they do not assume the actual spin Hamiltonian identification.

**Remaining work:** Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

### V108 Physical free plane-wave and Slater energy

**Status:** Checked in Lean within the stated scope. **Priority:** actual free-point Slater construction.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Are the exact phase,operator or determinant identities proved with the required boundary and domain conditions explicit?

**Evidence:** The actual complex exponential plane wave on integer coordinates obeys nearest-neighbor hopping energy -cos(p). The actual consecutive-root momenta obey the correct periodic circle sign at every integer position. The exact free coordinate hopping operator acts on the finite plane-wave determinant with total energy equal to the sum of -cos(p_j). The coordinate operator is not yet identified with the actual spin-sector restriction.

**Remaining work:** Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

### V109 Actual consecutive Slater Vandermonde and nonvanishing

**Status:** Checked in Lean within the stated scope. **Priority:** actual free-point Slater construction.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Are the exact phase,operator or determinant identities proved with the required boundary and domain conditions explicit?

**Evidence:** The site Fourier phases are injective in one period. The actual consecutive-root Slater determinant equals an explicitly row-scaled Vandermonde determinant. Therefore every distinct-site configuration within one period has nonzero amplitude. All casts,phase factors,and the empty-particle case are retained;no Bethe-state correspondence is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

### V110 Configuration-independent phase and strictly positive free Slater amplitudes

**Status:** Checked in Lean within the stated scope. **Priority:** actual free-point Slater construction.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Are the exact phase,operator or determinant identities proved with the required boundary and domain conditions explicit?

**Evidence:** The site-phase difference has an exact sine factorization. The ordered-pair phase sum counts each coordinate n-1 times,so all configuration-dependent phases cancel. The actual consecutive-root Slater determinant equals one nonzero constant depending only on n times the real sine Vandermonde. Dividing by this single constant makes every ordered configuration within one period real and strictly positive. This constructs the positive candidate used in the free-point argument;the actual spin-operator and Bethe identifications remain open.

**Remaining work:** Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

### V111 Actual spin words and ordered particle coordinates

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** The nested physical spin words are explicitly equivalent to Fin L site-bit functions. The actual particle count equals the sum of site bits and the cardinality of the occupied-site set. Its increasing enumeration gives strictly increasing integer coordinates in[0,L). The earlier positive free Slater construction therefore defines an actual spin-sector vector with real,strictly positive amplitudes and a proved nonzero value. Arbitrary site permutations preserve the actual particle count. All9 formerly prepared coordinate results are integrated once.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V112 Exact coordinates of allowed adjacent physical exchanges

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** An exchange between an occupied site and an adjacent hole preserves order of the occupied-site enumeration. The exact integer coordinate map of the actual exchanged spin configuration is Function.update at the corresponding particle index by +1 or -1. Order preservation uses the missing target site explicitly;the formulas do not assume the desired Hamiltonian identity.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V113 Exact physical first-bond hopping action

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** The first-pair link matrix equals an exact translate of the seam term in the actual logarithmic Hamiltonian. At lambda=pi/2 and eta=1/2 the actual local R-derived link has only particle-hole exchange entries,equal to -1/2. Its full-spin matrix action is exactly that exchange when the two spins differ,and zero otherwise.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V114 Full actual periodic free Hamiltonian hopping action

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** Every actual Hamiltonian bond is the first physical bond evaluated on rotated configurations. Reindexing the finite matrix sum proves the FULL row-derived Hamiltonian acts by the sum of its allowed periodic spin exchanges,each with coefficient -1/2. These are exact operator statements for all spin vectors. All rotations and exchanges preserve the actual particle count.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V115 Actual cyclic translation in finite site coordinates

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** Appending a physical last spin is exactly Fin.snoc of the site-bit tuple. The actual cyclicSpinTranslation is precisely finRotate of the same finite site bits,including its endpoint. The identity is proved for every translation power and every actual spin configuration.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V116 Fermionic boundary signs cancel exactly

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** A coordinate permutation multiplies the plane-wave determinant by its exact permutation sign. Moving a single particle by one full spatial period multiplies it by (-1)^(particle_count-1),using the actual consecutive-root circle condition. Moving the first particle once around the circle and cyclically putting it last has no sign:these two proved factors cancel. No periodic-boundary sign is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V117 Actual complex sector Hamiltonian hopping action

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** Extending a particle-sector vector by zero turns the exact restricted Hamiltonian action into the full actual physical action. The actual periodic bond exchanges restrict to the same sector. Applying the proved full action gives the exact allowed-exchange sum for the actual complex sector Hamiltonian,without assuming a coordinate-operator or eigenvector identity.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V118 Literal periodic sites of every actual Hamiltonian bond

**Status:** Checked in Lean within the stated scope. **Priority:** actual free spin Hamiltonian and coordinate bridge.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is this identity proved for the actual spin configurations,site labels,operator or root phase,with every needed hypothesis explicit?

**Evidence:** The actual bond-rotation permutation is tracked on the actual finite site-bit tuple. Bond k connects precisely the literal sites k-1 and k modulo L. Every actual physical bond exchange is exactly the corresponding site transposition. The full actual Hamiltonian therefore has an explicit site-hopping formula:sum over k of -1/2 times the vector at the swapped configuration when the site bits differ. This is an exact identity for the row-derived operator,not a replacement model.

**Remaining work:** Whole Lemma3.1 remains partial. Positive free Slater amplitudes,actual ordered spin coordinates,all interior adjacent-hop coordinate identities,exact full and sector physical Hamiltonian hopping formulas,and the fermionic wrap sign cancellation are proved. Remaining free-point bridge:identify the boundary exchanges with the sorted particle-coordinate wrap and reindex the literal site-hopping sum into the free coordinate-hopping sum. Then the positive candidate will satisfy the actual Hamiltonian eigenvalue equation. Still identify the actual Bethe vector with that ground line and justify continuation in lambda. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V119 Exact sorted boundary coordinates and physical Slater amplitudes

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** A physical left boundary exchange removes the first occupied coordinate at zero and appends the empty final spatial site. The reverse right exchange prepends zero and removes the final occupied coordinate. Both exact sorted-coordinate maps are proved from the actual occupied-site enumeration. Combining them with the proved fermionic cyclic-wrap cancellation gives the exact covering-line Slater amplitude for both physical boundary exchanges. The3 formerly prepared boundary-coordinate results are integrated once.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V120 Uniform actual left and right Slater hop amplitudes

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** The occupied index at spatial zero must be the first particle index,and the occupied index at the final spatial site must be the last. These facts combine the proved interior and boundary formulas into one exact Slater amplitude for every allowed left or right physical particle-hole exchange.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V121 Actual Hamiltonian reindexed by occupied particles

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** The increasing occupied-site enumeration is a genuine finite sum correspondence. The actual complex sector Hamiltonian first has the exact literal-site formula and then is reindexed into one left and one right move per occupied particle. The proof explicitly splits the two possible unequal site bits and uses the exact site-swap symmetry and periodic reindexing. Empty sectors are included. No coordinate-Hamiltonian correspondence is assumed.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V122 All blocked Slater hops vanish including the seam

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** Every occupied physical site has a particle index. Moving one labeled coordinate onto another gives an exactly zero determinant. A plus or minus full-period shift preserves this zero by the actual consecutive-root circle condition. Consequently every blocked right or left move gives zero,including a move across the periodic seam. Spatial length at least2 is explicit.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V123 Actual free Slater spin-Hamiltonian eigenvalue equation

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** Allowed-hop amplitudes and blocked zeros identify the ACTUAL complex spin-sector Hamiltonian action on the constructed Slater state with the proved free coordinate Hamiltonian action. Applying the already proved determinant eigenvalue theorem gives the actual spin-sector eigenvector equation with energy equal to the sum of -cos(p_j). Every physical bond,periodic boundary and collision case is proved.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V124 Actual free Slater simple ground-state line

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** Two strictly positive eigenvectors of a finite real symmetric matrix have the same eigenvalue,proved by the positive dot product and symmetry. The real part of the constructed Slater vector satisfies the exact real-sector eigenvalue equation. Comparing it with the previously constructed actual positive minimum proves that its energy is the actual ground energy. The complete complex energy lower bound and simple entire complex eigenspace are proved for this specific Slater state. This is the Slater ground line;the ABA Bethe-vector identification is still open.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

### V125 Differentiate the actual transfer eigenline into the Hamiltonian eigenline

**Status:** Checked in Lean within the stated scope. **Priority:** actual free Slater ground-state line.

**Location:** [sections/03-thermodynamic-kernels.tex:449](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/03-thermodynamic-kernels.tex#L449), `lem:root-limits,free-point ground-state argument`.

**Question:** Is the actual spin operator,eigenvector,minimum or derivative identity proved with the necessary hypotheses explicit?

**Evidence:** An exact finite matrix eigenline is differentiated entry by entry. A proved algebraic logarithmic-derivative lemma uses the actual inverse translation and nonzero eigenmatrix to show that the transfer eigenvalue at the swap is nonzero and that the actual Hamiltonian eigenvalue is -eta*rho_prime(0)/rho(0). The actual homogeneousPhysicalRow derivative and homogeneousLinkHamiltonian definitions instantiate this identity. The remaining Bethe energy calculation can therefore use the existing entire physical Bethe eigenmatrix directly.

**Remaining work:** Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed.

## Formalization boundary

5 of 51 named statements are proved in their stated setting: [Lemma 2.1, Finite row algebra](../lean/SixVertex/FiniteRowAlgebra.lean), [Lemma 2.3, Single-entry actions](../lean/SixVertex/SingleEntryActions.lean), [Lemma 2.2, Finite Bethe data](../lean/SixVertex/FiniteBetheData.lean), [Lemma 6.2, Convergence of representatives](../lean/SixVertex/ChiralRepresentatives.lean), [Lemma 7.6, Logarithmic integrability](../lean/SixVertex/LogIntegrability.lean). The representative-system and signed-measure lemmas do not establish the six-vertex limits to which they are applied. The clause correspondence is in [the named-statement record](../progress/named-statements.json).

[Lemma 2.4, Exact scalar products and deleted columns](../lean/SixVertex/ExactScalarProducts.lean), [Lemma 2.5, The Hilbert dual](../lean/SixVertex/HilbertDual.lean), [Corollary 2.6, Exact finite-word expansion](../lean/SixVertex/ExactFiniteWords.lean) are verified conditional only on A01, the user-authorized Slavnov identity, passed explicitly as a proposition. There are 43 other named statements without complete formalizations. Whole Lemma3.1 remains partial. The positive consecutive-momentum Slater state is now proved to be the ACTUAL free spin-sector Hamiltonian eigenvector and its simple ground-state line,with the lower energy bound for every complex sector vector. The full spin-coordinate action,all sorted boundary maps and blocked collision cases are complete. Still identify the actual ABA Bethe vector with that ground line by its coordinate formula or exact Hamiltonian energy,then justify continuation in lambda. The actual transfer-eigenline logarithmic derivative has now been proved for this purpose. The canonical actual Hamiltonian-ground/transfer-Perron certificate remains proved. U09 keeps the occupied compact-test qualification. No Bethe Perron conclusion is claimed. No unfinished estimate is assumed and no GFF theorem is represented as proved.

Duplicate-free column enumeration and normalized positive-rational single-column weights are proved. Real probability weights, the multi-column finite torus law and the exact transfer trace identity remain open. Global planar height integration is separate from local consistency. The 9 verification and scope-clarification items remain open.

An existing local scaffold was repaired and reused: its `TwoIncoming` predicate needed a decidability instance to compile with the installed toolchain. That was a code issue in the scaffold, not a mathematical gap in the OAI paper.
