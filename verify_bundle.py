#!/usr/bin/env python3
"""Verify every shipped file; this does not run Lean or prove mathematics."""
from pathlib import Path
import hashlib,sys
root=Path(__file__).resolve().parent
errors=[];count=0
for line in (root/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);p=root/name
 if not p.is_file():errors.append('Missing: '+name);continue
 if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:errors.append('Hash mismatch: '+name)
 count+=1
print('Bundle files checked:',count)
if errors:
 print('\n'.join(errors));sys.exit(1)
print('PASS: all bundled file hashes match. Run the Lean audit separately.')
