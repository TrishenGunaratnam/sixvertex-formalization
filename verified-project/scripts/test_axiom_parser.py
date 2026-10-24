"""Axiom audit regression: reject unexpected, malformed, or missing reports."""
import runpy
from pathlib import Path

parse = runpy.run_path(str(Path(__file__).with_name("check.py")))["parse_axiom_output"]

wrapped = "\n".join([
    "'SixVertex.long_theorem' depends on axioms: [propext,",
    " Classical.choice,",
    " Quot.sound]",
    "'SixVertex.constructive' does not depend on any axioms",
])
assert parse(wrapped) == (["SixVertex.long_theorem", "SixVertex.constructive"], [])
for bad in [
    "'SixVertex.bad' depends on axioms: [propext,\n sorryAx]",
    "'SixVertex.bad' depends on axioms: [Classical.choice,\n external_identity]",
    "'SixVertex.bad' depends on axioms: [propext,",
    "'SixVertex.bad' unexpected report format",
    "'SixVertex.duplicate' does not depend on any axioms\n" * 2,
]:
    assert parse(bad)[1], bad
print("Axiom parser regression checks PASS")
