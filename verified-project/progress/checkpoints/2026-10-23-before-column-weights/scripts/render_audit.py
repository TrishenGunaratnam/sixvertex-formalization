#!/usr/bin/env python3
"""Render the audit from evidence records; never turn proof presence into verification."""
import collections
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "audit/findings.json").read_text())
inventory = json.loads((ROOT / "audit/statement-inventory.json").read_text())
manifest = json.loads((ROOT / "sources/openai-math/SOURCE_MANIFEST.json").read_text())
paper = manifest["matched_six_vertex_directories"][0]
base = "https://github.com/openai/math/blob/" + manifest["commit"] + "/preprints/" + paper + "/build/"
status = {
    "checked_in_lean": "Checked in Lean within the stated finite scope",
    "citation_checked": "Cited statement located and checked; external proof not formalized",
    "proof_located_open": "Proof located; independent verification remains open"
}
lines = [
    "# Six vertex proof audit", "",
    "The 93-page OAI manuscript has been checked for its proof structure, source provenance, "
    "key external dependencies and selected delicate implications. The first pass establishes "
    "**no mathematical error**; it leaves **eight substantive verification items open**. "
    "These flags identify arguments to check, rather than declaring their conclusions false.", "",
    "The full-range Gaussian free field claim is not independently validated or formalized by this project.", "",
    "## Scope and source", "", data["scope"], "",
    "Source: the October OpenAI mathematics dump, commit `" + manifest["commit"] + "`. "
    "The PDF and all source files were downloaded directly from this revision; all 19 manuscript "
    "and repository-metadata files match the recorded Git blob and SHA-256 hashes. The directory "
    "scan found one manuscript title containing six-vertex. External papers below are reference "
    "checks, not alternative OAI source files.", "",
    "## Proof structure checks", "",
    "The TeX sources contain **51 named theorem, lemma, proposition or corollary statements** "
    "and **286 labels**. The structural scan found no duplicate labels, unresolved internal "
    "references, or missing bibliography keys. Presence of text under a proof environment is "
    "not verification of the proof.", "",
    "The four statements not followed immediately by a proof have deferred proofs: the main "
    "theorem in `08-main-proof.tex`; covariance normalization later in `05-normalization.tex`; "
    "the overlap asymptotic in that section's symbol calculation; and endpoint rotation later "
    "in `09-endpoint-rotation.tex`. They are not missing merely because the proofs are deferred.", "",
    "| Section | Named statements | First-pass review focus |", "|---|---:|---|"
]
focus = {
    "01": "Exact law, height normalization, test classes and parameter range",
    "02": "Gauge/adjoint conventions, Bethe data and cited determinant normalization",
    "03": "Sparse roots, uniform inverses, normalization and joint determinant tails",
    "04": "Boundary continuation, physical-law identification, orbit measures and Hamiltonian",
    "05": "Twist stiffness, infrared comparison, overlap jets and sampled symbol",
    "06": "All-zero control, representative convergence, collision and Wick recursion",
    "07": "Moment bounds, desmoothing, finite-energy tests and distinct function-space claims",
    "08": "Assembly order and conditional external normalization",
    "09": "Fair-signed FK correspondence, homotopy coupling, multiplicity and endpoint closure"
}
counts = collections.Counter(x["file"] for x in inventory["statements"])
build = ROOT / "sources/openai-math/preprints" / paper / "build"
for path in sorted((build / "sections").glob("*.tex")):
    number = path.name[:2]
    rel = "sections/" + path.name
    lines.append(f"| [{path.name}]({base+rel}) | {counts[rel]} | {focus[number]} |")
lines += ["", "## Evidence labels", "",
    "- **Checked in Lean:** the precisely described finite result compiles and its dependencies pass an axiom audit.",
    "- **Citation checked:** the external source really states the required kind of result, with its range and assumptions; its proof is not thereby revalidated.",
    "- **Proof located and open:** an argument is written in the manuscript, but its delicate implications still need independent verification.",
    "", "## Findings and remaining obligations", ""]
for finding in data["findings"]:
    lines += ["### " + finding["id"] + " " + finding["title"], "",
        "**Status:** " + status[finding["status"]] + ". **Priority:** " + finding["priority"] + ".", "",
        "**Location:** [" + finding["file"] + ":" + str(finding["line"]) + "](" + base + finding["file"] + "#L" + str(finding["line"]) + "), `" + finding["label"] + "`.", "",
        "**Question:** " + finding["question"], "",
        "**Evidence:** " + finding["evidence"], "",
        "**Remaining work:** " + finding["remaining"], ""]
    if finding.get("external_urls"):
        lines += ["References: " + ", ".join("[" + u.split("/")[-1] + "](" + u + ")" for u in finding["external_urls"]) + ".", ""]
lines += ["## Formalization boundary", "",
    "The current Lean library proves finite foundations. No analytic result is assumed as an "
    "axiom, and no GFF theorem is represented as proved. The first extension should establish "
    "duplicate-free enumeration, real Boltzmann weights, the finite torus law and the exact "
    "transfer trace identity. Global planar height integration is separate from local consistency.", "",
    "An existing local scaffold was repaired and reused: its `TwoIncoming` predicate needed "
    "a decidability instance to compile with the installed toolchain. That was a code issue "
    "in the scaffold, not a mathematical gap in the OAI paper.", ""]
(ROOT / "audit/REPORT.md").write_text("\n".join(lines))
print("Rendered audit report with", len(data["findings"]), "evidence records.")
