#!/usr/bin/env python3
"""Build all starter results, inspect their axioms, and verify source provenance."""
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
            r"(?m)^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)", code)]
        if re.search(r"\b(sorry|admit|axiom|unsafe)\b", code):
            forbidden.append(str(path.relative_to(ROOT)))
    (LEAN / "Audit.lean").write_text("import SixVertex\n\n" +
        "\n".join("#print axioms " + name for name in names) + "\n")
    build = run(["lake", "build"])
    audit = run(["lake", "env", "lean", "Audit.lean"]) if build["exit_code"] == 0 else None
    axiom_errors = []
    checked_names = []
    if audit:
        for line in audit["output"].splitlines():
            if line.startswith("'SixVertex."):
                checked_names.append(line.split("'")[1])
                if "depends on axioms:" in line:
                    used = {x.strip() for x in line.split("[")[-1].rstrip("]").split(",")}
                    if not used <= ALLOWED:
                        axiom_errors.append(line)
        if set(checked_names) != set(names):
            axiom_errors.append("The axiom audit did not report every declared theorem.")
    passed = not source_errors and not forbidden and build["exit_code"] == 0 and bool(audit) \
        and audit["exit_code"] == 0 and not axiom_errors
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
        "scope": "Finite foundations only. No named main-paper analytic theorem or GFF limit is formalized."
    }
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Sources: {len(manifest['files'])} files checked; mismatches: {len(source_errors)}")
    print(f"Lean: {len(names)} foundational theorems; build and axiom audit: {'PASS' if passed else 'FAIL'}")
    print(result["scope"])
    if not passed:
        print(build["output"])
        if audit:
            print(audit["output"])
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
