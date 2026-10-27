#!/usr/bin/env python3
"""Read-only integrity check; not mathematical verification."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'MANIFEST.json').read_text())
for row in manifest['files']:
    rel = Path(row['path'])
    assert not rel.is_absolute() and '..' not in rel.parts, rel
    path = root / rel
    assert not path.is_symlink() and path.is_file(), rel
    data = path.read_bytes()
    assert len(data) == row['bytes'], rel
    assert hashlib.sha256(data).hexdigest() == row['sha256'], rel
print(f"PASS: {len(manifest['files'])} payload files match the manifest")
