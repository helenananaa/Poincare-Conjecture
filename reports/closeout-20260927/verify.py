#!/usr/bin/env python3
"""Verify published source hashes; this does not replace Lean kernel checking."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

def verify_rows(rows):
    for entry in rows:
        path = (REPO / entry['path']).resolve()
        if not path.is_relative_to(REPO) or not path.is_file():
            raise ValueError('Missing or unsafe path: ' + entry['path'])
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry['sha256']:
            raise ValueError('Hash mismatch: ' + entry['path'])

if __name__ == '__main__':
    try:
        sources = json.loads((HERE / 'source-manifest.json').read_text())['sources']
        locks = json.loads((HERE / 'frozen-records.json').read_text())['records']
        verify_rows(sources)
        verify_rows(locks)
        print(json.dumps({'source_hash_check': 'PASS', 'sources': len(sources),
            'frozen_records': len(locks), 'lean_rebuild_performed': False,
            'poincare_complete': False}, indent=2))
    except (OSError, ValueError, KeyError) as error:
        print('PUBLICATION_CHECK_FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
