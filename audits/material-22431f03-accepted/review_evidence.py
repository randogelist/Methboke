"""Nonexecuting evidence review: JSON, text and hashes only; never runs Lean."""
import gzip, hashlib, json, pathlib, re

BASE = pathlib.Path(__file__).resolve().parent
EVIDENCE = BASE / 'evidence'
SHA = '22431f032c868b8de1526767d7d32a2639f6a9ee'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
report = json.loads((EVIDENCE / 'current.json').read_text())
expected = json.loads((BASE / 'expected-manifests.json').read_text())
checks = 0
def check(condition, detail):
    global checks
    assert condition, detail
    checks += 1
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def norm(text):
    return ' '.join(text.split())

check(digest(BASE/'evidence.zip') == 'ba080a4d4348de6e2dfe78facf777bb3b74d3aa3f10bd4757163b39f13c35532', 'ZIP digest')
check((BASE/'evidence.zip').stat().st_size == 212745, 'ZIP size')
check(report['commit'] == SHA and report['run_id'] == '44641040255', 'exact run identity')
check(report['status'] == 'PASS' and report['all_endpoints_selected'] and report['fresh_required_audits'], 'complete run PASS')
check(report['toolchain'] == 'leanprover/lean4:v4.33.0', 'compiler pin')
check(report['mathlib_commit'] == 'db584cd6d46c92f209a44c0f1c829460d327499d', 'Mathlib pin')
check(report['source_pin_integrity'] and all(x['tracked_source_clean'] for x in report['verified_dependencies']), 'dependency source identity')
check(report['platform'] == {'machine':'x86_64','system':'Linux'}, 'platform')
check(len(report['module_receipts']) == 411 and all(x['status'] == 'PASS' for x in report['module_receipts'].values()), '411 PASS module receipts')
check(sum(x['reused'] for x in report['module_receipts'].values()) == 392, '392 reused modules')
check(report['metrics']['fresh_module_count'] == 19, '19 fresh modules')
check(report['metrics']['audit_fresh_count'] == 71 and report['metrics']['audit_reused_count'] == 0, 'all 71 package audits fresh')
actual = {e['id']: e for e in report['endpoints']}
check(len(actual) == len(report['endpoints']) == len(expected) == 71, '71 unique packages')
check(set(actual) == {e['id'] for e in expected}, 'exact configured package set')
named = 0
names_seen = []
packages = []
for spec in expected:
    entry = actual[spec['id']]
    names = [x['name'] for x in spec['declarations']]
    names_seen.extend(names)
    named += len(names)
    check(entry['status'] == 'PASS' and entry['source_drift'] == [], spec['id'] + ' status/source')
    check(set(spec['allowed_axioms']) == STANDARD, spec['id'] + ' allowed policy')
    check(entry['audit_origin_commit'] == SHA and entry['audit_reused'] is False, spec['id'] + ' fresh identity')
    check(entry['declaration_count'] == len(names) == len(set(names)), spec['id'] + ' exact count')
    check(set(entry['types']) == set(names) == set(entry['axioms']), spec['id'] + ' expected names')
    log = EVIDENCE / entry['audit_log'].removeprefix('registry/')
    check(digest(log) == entry['audit_sha256'], spec['id'] + ' log hash')
    text = log.read_text()
    check(not re.search(r'\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror(?:\([^\n)]*\))?\s*:',text,re.I), spec['id'] + ' no errors/admissions')
    sentinels = re.findall(r'^(TYPE_BEGIN|TYPE_END|AXIOMS_BEGIN|AXIOMS_END):(.*)$', text, re.M)
    expected_sentinels = [(s,n) for n in names for s in ['TYPE_BEGIN','TYPE_END','AXIOMS_BEGIN','AXIOMS_END']]
    check(sentinels == expected_sentinels, spec['id'] + ' exact unique ordered coverage')
    for name in names:
        body = re.search(r'^TYPE_BEGIN:' + re.escape(name) + r'\n(.*?)\nTYPE_END:' + re.escape(name) + r'$', text, re.M|re.S).group(1)
        check(norm(body) == norm(entry['types'][name]), name + ' type report/log equality')
        body = re.search(r'^AXIOMS_BEGIN:' + re.escape(name) + r'\n(.*?)\nAXIOMS_END:' + re.escape(name) + r'$', text, re.M|re.S).group(1)
        m = re.fullmatch("'"+re.escape(name)+r"'\s+depends on axioms:\s*\[([^\]]*)\]", body.strip(), re.S)
        if m:
            deps = {re.sub(r'\.\{[^}]*\}', '', s.strip()) for s in m.group(1).split(',') if s.strip()}
        else:
            check(re.fullmatch("'"+re.escape(name)+r"'\s+does not depend on any axioms\.?",body.strip()) is not None,name+' axiom grammar')
            deps = set()
        check(deps <= STANDARD and deps == set(entry['axioms'][name]), name + ' allowed exact axiom report')
    packages.append({'id':spec['id'],'declarations':len(names),'audit_sha256':entry['audit_sha256']})
check(named == 448, '448 named audits')
cutout=report['cutout']
check(cutout['status']=='PASS' and cutout['audit_origin_commit']==SHA and cutout['audit_reused'] is False, 'QFB fresh PASS')
check(digest(EVIDENCE/cutout['audit_log'].removeprefix('registry/')) == cutout['audit_sha256'], 'QFB log hash')
check(set(cutout['axioms']) == {'QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED'}, 'QFB name')
check(set(next(iter(cutout['axioms'].values()))) <= STANDARD, 'QFB allowed axioms')
qfbtext=(EVIDENCE/cutout['audit_log'].removeprefix('registry/')).read_text()
check('sorryAx' not in qfbtext and 'QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED' in qfbtext,'QFB raw log')
fast=gzip.decompress((BASE/'fast-job.log.gz').read_bytes()).decode() if (BASE/'fast-job.log.gz').exists() else (BASE/'fast-job.log').read_text()
accepted=(BASE/'accepted-job.log').read_text()
check('PRIMARY_ACCEPTED: true' in accepted and 'PRIMARY_RESULT: success' in accepted and 'PRIMARY_FAILURE_CLASS: NONE' in accepted,'final gate context')
check('id=worker.publish_binary;outcome=success;conclusion=success' in fast,'binary publication')
check('id=worker.published_identities;outcome=success;conclusion=success' in fast,'cache identity publication')
check('id=worker.final_evidence;outcome=success;conclusion=success' in fast,'final evidence publication')
summary={
    'schema_version':1,'status':'CHECKED_EVIDENCE_CONSISTENT','review_kind':'independent_nonexecuting_text_json_hash_review',
    'tested_commit':SHA,'run_id':44641040255,'run_url':report['run_url'],
    'primary_job_id':135971854575,'accepted_job_id':135978130987,
    'artifact_id':14587751135,'artifact_bytes':212745,'artifact_sha256':digest(BASE/'evidence.zip'),
    'report_sha256':digest(EVIDENCE/'current.json'),'checks_passed':checks,
    'module_count':411,'reused_modules':392,'fresh_modules':19,'fresh_package_audits':71,
    'named_audits':448,'unique_named_declarations':len(set(names_seen)),'qfb_cutout_audit':True,
    'allowed_axioms':sorted(STANDARD),'all_audits_fresh':True,'all_raw_log_hashes_match':True,
    'all_expected_names_matched_to_pinned_manifests':True,'final_gate_pass':True,'publication_pass':True,
    'compiler':report['compiler'],'toolchain':report['toolchain'],'mathlib_commit':report['mathlib_commit'],
    'metrics':report['metrics'],'total_seconds':report['total_seconds'],
    'dependency_cache_class':report['dependency_cache_class'],'project_cache_class':report['project_cache_class'],
    'module_workers':report['module_workers'],'lean_threads':report['lean_num_threads'],
    'new_ehrenfest_declarations':75,'cumulative_ehrenfest_declarations':183,
    'accepted_new_milestone':'E10','accepted_new_helper':'E09.bound',
    'conditional_root':True,'stopped_witness_proved':False,'full_operator_translation_proved':False,'full_E09_H2_convergence_proved':False,
    'root_type':actual['EhrenfestObstructionRoot']['types']['MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION'],
    'root_axioms':actual['EhrenfestObstructionRoot']['axioms']['MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION'],
    'root_audit_sha256':actual['EhrenfestObstructionRoot']['audit_sha256'],
    'E09_bound_audit_sha256':actual['EhrenfestEventualEnstrophyBound']['audit_sha256'],
    'packages':packages,'local_lean_executions':0,
    'limits':['Does not rerun Lean or verify kernel objects locally.','Compiled source and complete independent consumer types audited externally at the recorded SHA.','Does not promote full operator E01-E06 or full H2 E09 milestones.']
}
(BASE/'independent-review.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['packages','metrics']},indent=2,ensure_ascii=False))
