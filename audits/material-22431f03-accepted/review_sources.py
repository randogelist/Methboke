"""Read-only hash/import/sentinel review; does not execute Lean or Lake."""
import hashlib, json, pathlib
base = pathlib.Path(__file__).resolve().parent
data = json.loads((base / 'pinned-source-review-inputs.json').read_text())
expected = {x['id']: x for x in json.loads((base / 'expected-manifests.json').read_text())}
checks = 0
sources = []
for row in data:
    raw = row['content'].encode()
    sha = hashlib.sha256(raw).hexdigest()
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['blob_sha'], row['path']
    checks += 1
    if row['kind'] == 'owned_source':
        assert sha == row['expected_sha256'], row['path']
        checks += 1
        imports = []
        for line in row['content'].splitlines():
            if line.startswith('import '):
                imports.extend(line[7:].split())
        assert imports == row['imports'], row['path']
        checks += 1
    elif row['kind'] == 'Audit':
        for declaration in expected[row['package']]['declarations']:
            for prefix in ['TYPE_BEGIN:', 'TYPE_END:', 'AXIOMS_BEGIN:', 'AXIOMS_END:']:
                assert row['content'].count('"' + prefix + declaration['name'] + '"') == 1
                checks += 1
        assert 'set_option autoImplicit false' in row['content']
        checks += 1
    sources.append({k: v for k, v in row.items() if k not in ['content', 'imports']} | {'actual_sha256': sha})
retained = json.loads((base / 'source-review.json').read_text())
assert checks == retained['source_hash_checks_passed'] == 534
assert sources == retained['sources']
print(json.dumps({'status': 'PASS', 'checks': checks, 'owned_sources': 71, 'new_wrapper_sources': 14, 'local_lean_executions': 0}))
