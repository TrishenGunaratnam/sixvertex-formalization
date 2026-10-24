# Six vertex proof audit

The 93-page OAI manuscript has been checked for its proof structure, source provenance, key external dependencies and selected delicate implications. The first pass establishes **no mathematical error**; it leaves **eight substantive verification items open**. These flags identify arguments to check, rather than declaring their conclusions false.

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

- **Checked in Lean:** the precisely described finite result compiles and its dependencies pass an axiom audit.
- **Citation checked:** the external source really states the required kind of result, with its range and assumptions; its proof is not thereby revalidated.
- **Proof located and open:** an argument is written in the manuscript, but its delicate implications still need independent verification.

## Findings and remaining obligations

### V01 Arrow convention and local height consistency

**Status:** Checked in Lean within the stated finite scope. **Priority:** foundation.

**Location:** [sections/01-introduction.tex:22](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/01-introduction.tex#L22), `Height convention`.

**Question:** Does the two-in/two-out rule give the stated unit height increments, with consistent signs?

**Evidence:** The starter Lean code proves equivalence of the ice rule and two incoming arrows; equivalence with zero elementary height circulation; construction and uniqueness of four adjacent face heights with a chosen anchor; and periodic-column sector conservation.

**Remaining work:** Global integration over a simply connected domain, the infinite planar law and torus winding periods remain outside these local proofs. No full paper theorem is certified by this check.

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

**Remaining work:** Independently verify every normalization, slot order, pole cancellation and analytic specialization. The original theorem's presence does not by itself verify those conversions or all root-of-unity specializations.

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

**Evidence:** Separate proofs are supplied for finite-energy measures, restriction Besov/Hölder/Sobolev norms, the source's outward-scaling completion, and intrinsic Sobolev duals on arbitrary bounded open sets. The finite-energy proof includes the case where distinct continuum points round to the same lattice face. The intrinsic proof treats small-area cells by a thick/thin decomposition.

**Remaining work:** Fix exact definitions of each negative Sobolev realization before formalization. Independently check logarithmic domination, mollification in energy, separability, compactness, pinning and thin-cell estimates. The phrase 'usual ... realization' needs an explicit definition; these spaces must not be silently identified on irregular domains.

### U08 Endpoint rotation requires a loop bijection, not just close loop sets

**Status:** Proof located; independent verification remains open. **Priority:** high.

**Location:** [sections/09-endpoint-rotation.tex:276](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/09-endpoint-rotation.tex#L276), `lem:rr-nails; thm:rr-rotation; prop:endpoint-completion`.

**Question:** Does the external FK rotation argument preserve multiplicity and endpoint separation information?

**Evidence:** The appendix deliberately uses the homotopy coupling before its metric conclusion. The cited rotation paper, arXiv:2012.11672v2, Definition 3.8 and Sections 3.5-3.6, does define homotopic similarity using a bijection of nontrivial loops and matching crossing words. Lis arXiv:2004.05337v2, Lemma 3.1, supplies the stated infinite-volume loop-law convergence at c=2. The OAI appendix includes fair-sign averaging, loop counts, point avoidance and a nail-window extraction.

**Remaining work:** Verify the full extracted coupling with its exact marginals, parameter scales, orientations and multiplicities; the inside/outside transfer; and uniform integrability of the sign-averaged polynomial. The external set-distance rotation theorem alone would not prove this step. The complete extraction is not independently verified here.

References: [2012.11672v2](https://arxiv.org/html/2012.11672v2), [2004.05337v2](https://arxiv.org/html/2004.05337v2).

## Formalization boundary

The current Lean library proves finite foundations. No analytic result is assumed as an axiom, and no GFF theorem is represented as proved. The first extension should establish duplicate-free enumeration, real Boltzmann weights, the finite torus law and the exact transfer trace identity. Global planar height integration is separate from local consistency.

An existing local scaffold was repaired and reused: its `TwoIncoming` predicate needed a decidability instance to compile with the installed toolchain. That was a code issue in the scaffold, not a mathematical gap in the OAI paper.
