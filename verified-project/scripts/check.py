#!/usr/bin/env python3
"""Build all results, inspect every theorem's axioms, and verify source provenance."""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
REPORT = ROOT / "progress" / "verification.json"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def run(args):
    result = subprocess.run(args, cwd=LEAN, text=True, capture_output=True)
    return {"command": args, "exit_code": result.returncode,
            "output": result.stdout + result.stderr}


def parse_axiom_output(output):
    """Read complete Lean axiom reports, including pretty-printed line wraps."""
    pattern = r"(?m)^'(SixVertex\.[^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    checked, errors = [], []
    for match in re.finditer(pattern, output):
        checked.append(match.group(1))
        if match.group(2) is not None:
            used = {x.strip() for x in match.group(2).split(",") if x.strip()}
            if not used <= ALLOWED:
                errors.append(match.group(0))
    headers = re.findall(r"(?m)^'(SixVertex\.[^']+)'", output)
    if headers != checked:
        errors.append("Malformed or incomplete Lean axiom report.")
    if len(checked) != len(set(checked)):
        errors.append("Duplicate Lean axiom report.")
    return checked, errors


def main():
    manifest_root = ROOT / "sources" / "openai-math"
    manifest = json.loads((manifest_root / "SOURCE_MANIFEST.json").read_text())
    source_errors = []
    for item in manifest["files"]:
        data = (manifest_root / item["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != item["git_blob_sha1"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            source_errors.append(item["path"])

    names = []
    forbidden = []
    for path in sorted((LEAN / "SixVertex").glob("*.lean")):
        text = path.read_text()
        # The present files have no nested comments. Strip documentation before scanning.
        code = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
        code = re.sub(r"/-.*?-/", "", code, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        names += ["SixVertex." + name for name in re.findall(
            r"(?m)^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)", code)]
        if re.search(r"\b(sorry|admit|axiom|unsafe)\b", code):
            forbidden.append(str(path.relative_to(ROOT)))
    (LEAN / "Audit.lean").write_text("import SixVertex\n\n" +
        "\n".join("#print axioms " + name for name in names) + "\n")
    build = run(["lake", "build"])
    audit = run(["lake", "env", "lean", "Audit.lean"]) if build["exit_code"] == 0 else None
    axiom_errors = []
    checked_names = []
    if audit:
        checked_names, axiom_errors = parse_axiom_output(audit["output"])
        if set(checked_names) != set(names):
            axiom_errors.append("The axiom audit did not report every declared theorem.")
    named_expected = {"lem:row-algebra": "SixVertex.finite_row_algebra",
                      "lem:finite-actions": "SixVertex.single_entry_actions",
                      "lem:bethe-data": "SixVertex.finite_bethe_data",
                      "lem:chiral-representatives": "SixVertex.chiral_representatives",
                      "lem:log-integrability": "SixVertex.log_integrability"}
    conditional_expected = {"lem:scalar-product": "SixVertex.exact_scalar_products_and_deleted_columns",
                            "lem:hilbert-dual": "SixVertex.hilbert_dual",
                            "cor:finite-word-expansion": "SixVertex.exact_finite_word_expansion"}
    assumptions = json.loads((ROOT / "progress/assumptions.json").read_text())["assumptions"]
    named_errors = [label for label, name in {**named_expected, **conditional_expected}.items()
                    if name not in names or name not in checked_names]
    passed = not source_errors and not forbidden and build["exit_code"] == 0 and bool(audit) \
        and audit["exit_code"] == 0 and not axiom_errors and not named_errors
    result = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": manifest["commit"],
        "source_files_checked": len(manifest["files"]),
        "source_errors": source_errors,
        "lean_version": run(["lean", "--version"])["output"].strip(),
        "theorem_count": len(names), "theorems": names,
        "allowed_axioms": sorted(ALLOWED), "axiom_errors": axiom_errors,
        "forbidden_source_files": forbidden, "build": build, "axiom_audit": audit,
        "passed": passed,
        "scope": "Finite six-vertex foundations; Lemmas 2.1, 2.2 and 2.3 without external mathematical assumptions; Lemmas 2.4 and 2.5 and Corollary 2.6 conditional on the user-authorized Slavnov identity; their stated unconditional operator and norm identities are proved separately. Lemma 6.2 is proved for arbitrary dense representative systems with Gram convergence. Lemma 7.6 is proved for finite signed measures with ordinary absolute Green integrability, including the mixed-energy clause and the infinite diagonal. The six-vertex tensor construction and GFF limit are not formalized.",
        "named_statement_errors": named_errors,
        "named_paper_statements_checked": [
            {"paper_label": label, "lean_theorem": name, "checked": name in checked_names and passed}
            for label, name in named_expected.items()
        ],
        "conditional_named_paper_statements_checked": [
            {"paper_label": label, "lean_theorem": name, "checked": name in checked_names and passed,
             "assumptions": ["A01: SixVertex.SlavnovIdentity"]}
            for label, name in conditional_expected.items()
        ],
        "assumed_results": assumptions,
        "mathlib_revision": next(p["rev"] for p in json.loads(
            (LEAN / "lake-manifest.json").read_text())["packages"] if p["name"] == "mathlib")
    }
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Sources: {len(manifest['files'])} files checked; mismatches: {len(source_errors)}")
    print(f"Lean: {len(names)} theorems; build and axiom audit: {'PASS' if passed else 'FAIL'}")
    print(result["scope"])
    if not passed:
        print(build["output"])
        if audit:
            print(audit["output"])
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
