"""Compile the complete L-meta-4813 proof and independently check its statement and axioms."""
import os
import subprocess
import sys
from pathlib import Path

proof = Path(__file__).resolve().parent
project = proof.parent / 'lean'
objects = proof / '.build'
objects.mkdir(exist_ok=True)
modules = [
    'PNPBase', 'Core4813', 'MonotonePart', 'TenVerifier', 'Coordinates4813',
    'Geometry4813', 'Symmetry4813', 'Table4813', 'Pack4813', 'Roots4813',
    'Conditional4813', 'MonoTable', 'SignedTable', 'RootData4813',
    'MonoRows4813', 'BlockJoin4813',
    *(f'Level4813_{level}' for level in range(11, 17)),
    'SignedRowsAll', 'MonoFloor4813', 'Complete4813', 'Audit4813',
]
subprocess.run(['lake', 'build', 'PEqualNP.Outside.L_meta_670'], cwd=project, check=True)
lake_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=project, text=True).strip()
lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=project, text=True).strip()
env = os.environ.copy()
env['LEAN_PATH'] = str(objects) + os.pathsep + lake_path

for module in modules:
    print(f'Checking {module}', flush=True)
    src = proof / f'{module}.lean'
    out = objects / f'{module}.olean'
    subprocess.run([lean, '-j1', '--root=' + str(proof), '-o', str(out), str(src)],
                   cwd=project, env=env, check=True)
