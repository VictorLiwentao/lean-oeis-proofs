#!/usr/bin/env python3
"""Fresh serial A069004 rebuild using pinned Lean and installed dependencies."""
from pathlib import Path
import os, re, subprocess
root = Path(__file__).resolve().parents[1]
lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=root, text=True).strip()
out = root / '.lake/a069004-check/lib/lean'
out.mkdir(parents=True, exist_ok=True)
deps = sorted((root / '.lake/packages').glob('*/.lake/build/lib/lean'))
if not deps:
    raise SystemExit('Install dependencies first: lake exe cache get')
env = {**os.environ, 'LEAN_NUM_THREADS': '1',
       'LEAN_PATH': os.pathsep.join(map(str, [out, *deps]))}
seen = set()
def build(name):
    if name in seen:
        return
    source = root / (name.replace('.', '/') + '.lean')
    if not source.is_file():
        return
    seen.add(name)
    for dependency in re.findall(r'^import\s+([A-Za-z0-9_.]+)', source.read_text(), re.M):
        build(dependency)
    target = out / (name.replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    print('Checking', name, flush=True)
    subprocess.run([lean, '-DwarningAsError=true', '-DrelaxedAutoImplicit=false',
                    '-DmaxSynthPendingDepth=3', '-o', str(target),
                    str(source.relative_to(root))], cwd=root, env=env, check=True)
build('LeanOeisProofs.NewFormalization.A069004')
check = root / '.lake/a069004-check/Axioms.lean'
check.write_text('import LeanOeisProofs.NewFormalization.A069004\n' + ''.join(
    '#print axioms ' + name + '\n' for name in [
        'Cursor03R02.A069004.a_512720_ge', 'primeCounting_512720',
        'Cursor03R02.A069004.upper_bound_false', 'Cursor03R02.A069004.conjecture2']))
subprocess.run([lean, str(check)], cwd=root, env=env, check=True)
