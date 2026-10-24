#!/usr/bin/env python3
"""Regenerate the evidence-backed progress snapshot and an offline HTML copy."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
state = json.loads((ROOT / 'progress/state.json').read_text())
verification = json.loads((ROOT / 'progress/verification.json').read_text())
named = json.loads((ROOT / 'progress/named-statements.json').read_text())
assert state['paper_named_statements_formalized'] == named['fully_formalized']
assert state['paper_named_statements_remaining_unformalized'] == named['remaining_unformalized']
small_check = {k: verification[k] for k in ['source_files_checked', 'theorem_count', 'passed']}
fragment = (ROOT / 'progress/progress.template.html').read_text().replace(
    '__SIXVERTEX_STATE__', json.dumps(state)).replace(
    '__SIXVERTEX_VERIFICATION__', json.dumps(small_check))
fragment_path = ROOT / 'progress/progress.fragment.html'
fragment_path.write_text(fragment)

def links(results):
    return ', '.join('[' + r['paper_number'] + ', ' + r['title'] + '](../' + r['lean_file'] + ')'
                     for r in results)

completed = [r for r in named['results'] if r['status'] == 'formalized']
conditional = [r for r in named['results'] if 'conditional' in r['status']]
lines = ['# Six vertex progress', '', 'Updated ' + state['updated_on'] + '.', '',
    '**Main result: not proved in Lean.** The library contains ' + str(verification['theorem_count']) +
    ' checked Lean theorem declarations. ' + str(len(completed)) + ' of ' +
    str(state['paper_named_statements']) + ' named paper statements are proved in their stated setting. '
    'The helper count is not a percentage of the paper.', '',
    '**Completed:** ' + links(completed) + '. All clauses of these statements are checked. '
    'The six-vertex applications of the general representative and measure lemmas remain separate. '
    'See [the statement correspondence](named-statements.json).', '',
    '**Conditional:** ' + links(conditional) + ', with the sole external assumed input '
    '[A01, Slavnov identity](assumptions.json). There are ' + str(named['remaining_unformalized']) +
    ' other named statements without complete formalizations.', '',
    '| Milestone | Status | Next action |', '|---|---|---|']
for p in state['phases']:
    lines.append('| ' + p['title'] + ' | ' + p['status'].replace('_', ' ') + ' | ' + p['next'] + ' |')
lines += ['', '## Audit', '', 'First-pass structural and dependency review complete. ' +
    str(state['open_audit_items']) + ' verification and scope-clarification items remain open. '
    'No mathematical error has been established by this pass. '
    'See [the evidence records](../audit/REPORT.md).', '', '## Checks', '',
    'The build and all-theorem axiom audit ' + ('passed' if verification['passed'] else 'failed') +
    '; all ' + str(verification['source_files_checked']) + ' pinned source files were checked against '
    'their hashes. See [the machine-readable verification log](verification.json).', '',
    'The display is a saved snapshot. Re-run the checks and regenerate it after each development milestone.', '']
(ROOT / 'progress/STATUS.md').write_text('\n'.join(lines))
renderer = Path('/Users/trishengunaratnam/.codex/plugins/cache/openai-bundled/visualize/1.0.50/skills/visualize/scripts/render.py')
if renderer.exists():
    subprocess.run([sys.executable, str(renderer), str(fragment_path),
                    str(ROOT / 'progress/progress.html'), '--force'], check=True)
else:
    print('Inline fragment and Markdown status generated; standalone renderer unavailable.')
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(fragment)
print('Progress snapshot generated.')
