"""Pure routing, scope and receipt controls; execute only in external Actions CI.

These tests never invoke Lean, Lake, compiler/audit wrappers or a subprocess.
"""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "verify_theorem_goal.py"
SPEC = importlib.util.spec_from_file_location("theorem_goal_controls", SCRIPT)
goal = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(goal)
REVISION = "a" * 40


def environment(event="workflow_run"):
    return {"CI": "true", "GITHUB_ACTIONS": "true", "GITHUB_REPOSITORY": goal.REPOSITORY,
            "RUNNER_ENVIRONMENT": "github-hosted", "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64",
            "GITHUB_RUN_ID": "1234", "GITHUB_RUN_ATTEMPT": "1", "GITHUB_EVENT_NAME": event,
            "GITHUB_REF": "refs/heads/main", "GITHUB_SHA": REVISION}


def event_payload():
    return {"repository": {"full_name": goal.REPOSITORY}, "workflow_run": {
        "name": goal.UPSTREAM_WORKFLOW, "path": ".github/workflows/material.yml",
        "status": "completed", "conclusion": "success", "head_branch": "main",
        "head_repository": {"full_name": goal.REPOSITORY}, "head_sha": REVISION,
        "id": 9876, "run_attempt": 1}}


def endpoint(identifier, imports, modules, declarations=None):
    return {"id": identifier, "files": [{"module": name} for name in modules],
            "spec": {"imports": imports, "declarations": declarations or []}}


@unittest.skipUnless(os.environ.get("CI", "").lower() == "true"
                     and os.environ.get("GITHUB_ACTIONS", "").lower() == "true",
                     "These controls are executed only in the authorized external workflow.")
class TheoremGoalControls(unittest.TestCase):
    def test_workflow_run_uses_upstream_source_not_later_default_sha(self):
        env = environment()
        env["GITHUB_SHA"] = "b" * 40
        route = goal.validate_route(env, event_payload(), REVISION)
        self.assertEqual(route["upstream"]["source_revision"], REVISION)

    def test_rejects_failed_fork_wrong_branch_and_wrong_source_events(self):
        changes = (("conclusion", "failure"), ("head_branch", "AC-Integration"),
                   ("head_sha", "b" * 40), ("head_repository", {"full_name": "other/Methboke"}),
                   ("name", "Unrelated workflow"))
        for field, value in changes:
            with self.subTest(field=field):
                payload = event_payload()
                payload["workflow_run"][field] = value
                with self.assertRaises(goal.ScopeError):
                    goal.validate_route(environment(), payload, REVISION)

    def test_manual_dispatch_requires_exact_main_revision(self):
        env = environment("workflow_dispatch")
        self.assertIsNone(goal.validate_route(env, event_payload(), REVISION)["upstream"])
        for key, value in (("GITHUB_REF", "refs/heads/AC-Integration"), ("GITHUB_SHA", "b" * 40)):
            changed = dict(env, **{key: value})
            with self.assertRaises(goal.ScopeError):
                goal.validate_route(changed, event_payload(), REVISION)

    def test_r3_push_requires_full_parent_gate_and_exact_same_source(self):
        env = dict(environment("push"), GITHUB_REF="refs/heads/" + goal.R3_FOUNDATION_BRANCH,
                   GITHUB_WORKFLOW=goal.UPSTREAM_WORKFLOW, GITHUB_JOB=goal.R3_FOUNDATION_JOB,
                   MATERIAL_PARENT_ACCEPTED="true")
        event = {"repository": {"full_name": goal.REPOSITORY}, "after": REVISION, "deleted": False}
        route = goal.validate_route(env, event, REVISION)
        self.assertEqual(route["branch"], goal.R3_FOUNDATION_BRANCH)
        self.assertEqual(route["upstream"]["run_id"], env["GITHUB_RUN_ID"])
        self.assertEqual(route["upstream"]["source_revision"], REVISION)
        for field, value in (("GITHUB_REF", "refs/heads/main"),
                             ("GITHUB_SHA", "b" * 40),
                             ("GITHUB_WORKFLOW", "Unrelated workflow"),
                             ("GITHUB_JOB", "compile-audit-register"),
                             ("MATERIAL_PARENT_ACCEPTED", "false")):
            with self.subTest(field=field), self.assertRaises(goal.ScopeError):
                goal.validate_route(dict(env, **{field: value}), event, REVISION)
        for field, value in (("after", "b" * 40), ("deleted", True)):
            with self.subTest(field=field), self.assertRaises(goal.ScopeError):
                goal.validate_route(env, dict(event, **{field: value}), REVISION)

    def test_actual_checkout_must_match_routed_source(self):
        goal.validate_checkout_sha(REVISION + "\n", REVISION)
        with self.assertRaises(goal.ScopeError):
            goal.validate_checkout_sha("b" * 40, REVISION)

    def test_dependency_packages_expand_only_from_principal_source_closure(self):
        entries = [endpoint("Root", ["R"], ["R", "A", "B"]),
                   endpoint("Shared", ["A", "B"], ["A", "B", "Shared.Endpoint"]),
                   endpoint("Unrelated", ["A", "X"], ["A", "X"]),
                   endpoint("EmptyImports", [], [])]
        self.assertEqual(goal.select_scope(entries, {"principal_packages": ["Root"]}), ["Root", "Shared"])

    def test_a_definition_cannot_be_a_proved_root(self):
        row = {"id": "QFB", "root_declaration": "Root.target"}
        entry = endpoint("Root", ["R"], ["R"], [{"name": "Root.target", "kind": "definition"}])
        with self.assertRaises(goal.ScopeError):
            goal.root_contract(row, [entry])

    def test_target_definition_remains_distinct_from_proof(self):
        row = {"id": "WFA", "root_declaration": None, "target_definition": "Example.target"}
        entry = endpoint("Root", ["R"], ["R"], [{"name": "Example.target", "kind": "definition"}])
        contract = goal.root_contract(row, [entry])
        self.assertFalse(contract["target_definition_is_proof"])
        self.assertIsNone(contract["root_declaration"])
        entry["spec"]["declarations"][0]["kind"] = "theorem"
        with self.assertRaises(goal.ScopeError):
            goal.root_contract(row, [entry])

    def test_checked_in_manifest_keeps_open_roots_distinct_from_foundation_audits(self):
        root = SCRIPT.parents[1]
        manifest = json.loads((root / "Material/ci/theorem-goals.json").read_text())
        entries = [{"id": path.parent.name} for path in (root / "Material").glob("*/endpoint.json")]
        rows = goal.validate_manifest(manifest, entries)
        expected = ("WFA", "WFB", "QFA", "QFB", "SINGULAR_PREMISE_OBSTRUCT_R3", "SIGNULAR_PREMISE_OBSTRUCT_T3")
        self.assertEqual(set(rows), set(expected))
        self.assertEqual(goal.GOAL_IDS, expected)
        for identifier, status in {"WFA": "OPEN", "QFA": "OPEN_GENERAL_DATA"}.items():
            self.assertIsNone(rows[identifier]["root_declaration"])
            self.assertEqual(rows[identifier]["root_status"], status)
            self.assertEqual(rows[identifier]["ci_mode"], "placeholder")
            self.assertEqual(rows[identifier]["domain"], "R3")
        r3 = rows["SINGULAR_PREMISE_OBSTRUCT_R3"]
        self.assertIsNone(r3["root_declaration"])
        self.assertEqual(r3["root_status"], "OPEN_NO_NATIVE_ROOT")
        self.assertEqual(r3["ci_mode"], "foundation_audit")
        self.assertEqual(r3["target_definition"], "MethbokeAddon.R3Ehrenfest.NSE_A")
        self.assertTrue(r3["open_obligations"])
        self.assertTrue(r3["retained_foundation_scope"])
        for identifier in ("WFB", "QFB", "SIGNULAR_PREMISE_OBSTRUCT_T3"):
            self.assertEqual(rows[identifier]["ci_mode"], "audit")
            self.assertEqual(rows[identifier]["domain"], "T3")
        self.assertEqual(rows["SIGNULAR_PREMISE_OBSTRUCT_T3"]["root_status"],
                         "CONDITIONAL_SINGLE_PREMISE_ESTABLISHED")
        self.assertEqual(rows["SIGNULAR_PREMISE_OBSTRUCT_T3"]["open_obligations"], [])
        self.assertTrue(rows["SIGNULAR_PREMISE_OBSTRUCT_T3"]["retained_premises"])
        self.assertTrue(rows["SIGNULAR_PREMISE_OBSTRUCT_T3"]["separate_open_obligations"])
        missing_premises = copy.deepcopy(manifest)
        missing_premises["goals"][-1]["retained_premises"] = []
        with self.assertRaises(goal.ScopeError):
            goal.validate_manifest(missing_premises, entries)
        bad = copy.deepcopy(manifest)
        bad["goals"][0]["root_status"] = "EXACT_ROOT_ESTABLISHED"
        with self.assertRaises(goal.ScopeError):
            goal.validate_manifest(bad, entries)

        for field, value in (("root_declaration", "Pretend.proved_root"),
                             ("root_status", "EXACT_ROOT_ESTABLISHED"),
                             ("ci_mode", "audit"), ("open_obligations", []),
                             ("retained_foundation_scope", "")):
            bad = copy.deepcopy(manifest)
            next(row for row in bad["goals"] if row["id"] == r3["id"])[field] = value
            with self.subTest(field=field), self.assertRaises(goal.ScopeError):
                goal.validate_manifest(bad, entries)
        bad = copy.deepcopy(manifest)
        bad["goals"][0]["ci_mode"] = "foundation_audit"
        with self.assertRaises(goal.ScopeError):
            goal.validate_manifest(bad, entries)

    def _placeholder_main(self, goal_id):
        manifest = json.loads((SCRIPT.parents[1] / "Material/ci/theorem-goals.json").read_text())
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root, output = base / "checkout", base / "evidence"
            (root / "Material/ci").mkdir(parents=True)
            (root / "Material/ci/theorem-goals.json").write_text(json.dumps(manifest))
            for row in manifest["goals"]:
                for package in row["principal_packages"]:
                    path = root / "Material" / package / "endpoint.json"
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(json.dumps({"id": package}))
            event_path = base / "event.json"
            event_path.write_text(json.dumps(event_payload()))
            env = dict(environment(), GITHUB_EVENT_PATH=str(event_path), GITHUB_WORKSPACE=str(root),
                       GITHUB_STEP_SUMMARY=str(base / "summary.md"))
            arguments = [str(SCRIPT), "placeholder", "--goal", goal_id, "--revision", REVISION,
                         "--output", str(output)]
            with mock.patch.object(goal, "ROOT", root), mock.patch.dict(os.environ, env, clear=True), \
                    mock.patch.object(goal.sys, "argv", arguments), \
                    mock.patch.object(goal, "check_checkout") as checkout, \
                    mock.patch.object(goal, "load_drivers", side_effect=AssertionError("No drivers allowed")) as drivers, \
                    mock.patch.object(goal, "make_plan", side_effect=AssertionError("No audit planning allowed")) as planning, \
                    mock.patch.object(goal, "cached_preflight", side_effect=AssertionError("No cache allowed")) as cache, \
                    mock.patch.object(goal, "verify_goal", side_effect=AssertionError("No verification allowed")) as verify, \
                    mock.patch.object(goal.subprocess, "run", side_effect=AssertionError("No subprocess allowed")) as command, \
                    mock.patch("builtins.print"):
                result = goal.main()
                checkout.assert_called_once()
                for forbidden in (drivers, planning, cache, verify, command):
                    forbidden.assert_not_called()
            return result, json.loads((output / "scope-report.json").read_text()), (base / "summary.md").read_text()

    def test_placeholder_branch_never_loads_drivers_caches_or_compiler(self):
        for identifier, status in {"WFA": "OPEN", "QFA": "OPEN_GENERAL_DATA"}.items():
            with self.subTest(goal=identifier):
                result, report, summary = self._placeholder_main(identifier)
                self.assertEqual(result, 0)
                self.assertEqual(report["audit_status"], "DUMMY_PENDING")
                self.assertEqual(report["root_status"], status)
                self.assertIsNone(report["root_declaration"])
                self.assertFalse(report["compiler_executed"])
                self.assertFalse(report["cache_accessed"])
                self.assertEqual(report["fresh_package_count"], 0)
                self.assertEqual(report["fresh_named_reports"], 0)
                self.assertFalse(report["full_project_acceptance"])
                self.assertFalse(report["target_definition_is_proof"])
                if identifier == "QFA":
                    self.assertEqual(report["target_definition"],
                                     "MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA")
                self.assertIn("Dummy stage only", summary)

    def test_placeholder_command_rejects_a_real_audit_goal(self):
        for identifier in ("WFB", "QFB", "SIGNULAR_PREMISE_OBSTRUCT_T3", "SINGULAR_PREMISE_OBSTRUCT_R3"):
            with self.subTest(goal=identifier):
                result, report, _ = self._placeholder_main(identifier)
                self.assertEqual(result, 1)
                self.assertEqual(report["audit_status"], "FAIL")
                self.assertEqual(report["failure_class"], "PLACEHOLDER_MODE_REJECTED")
                self.assertFalse(report["compiler_executed"])

    def test_receipt_mismatch_is_read_only_and_never_reaches_a_compiler(self):
        records = {"Example": {"imports": [], "sha256": "source"}}
        old = {"Example": {"status": "PASS", "identity": "wrong", "object_files": {}}}
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            artifact = output / "Example.olean"
            artifact.write_bytes(b"retained-object")
            before = artifact.read_bytes()
            with mock.patch.object(goal.subprocess, "run", side_effect=AssertionError("No subprocess permitted")) as command:
                with self.assertRaises(goal.ScopeError) as caught:
                    goal.validate_receipts(records, old, {}, output, lambda *args: False)
                self.assertEqual(caught.exception.code, "CACHE_SCOPE_NOT_READY")
                command.assert_not_called()
            self.assertEqual(artifact.read_bytes(), before)

    def test_recursive_receipt_identity_binds_imported_object_bytes(self):
        records = {"A": {"imports": [], "sha256": "source-a"},
                   "B": {"imports": ["A"], "sha256": "source-b"}}
        context = {"compiler": "pinned"}
        identity_a = goal.fingerprint({"context": context, "source": "source-a", "module": "A", "imports": {}})
        receipt_a = {"status": "PASS", "identity": identity_a, "object_files": {"A.olean": "bytes-a"}}
        identity_b = goal.fingerprint({"context": context, "source": "source-b", "module": "B",
                                       "imports": {"A": {"identity": identity_a, "objects": receipt_a["object_files"]}}})
        receipt_b = {"status": "PASS", "identity": identity_b, "object_files": {"B.olean": "bytes-b"}}
        matches = lambda old, identity, path: old["identity"] == identity
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            self.assertEqual(set(goal.validate_receipts(records, {"A": receipt_a, "B": receipt_b},
                                                       context, output, matches)), {"A", "B"})
            receipt_a["object_files"]["A.olean"] = "changed-a"
            with self.assertRaises(goal.ScopeError):
                goal.validate_receipts(records, {"A": receipt_a, "B": receipt_b}, context, output, matches)

    def test_audit_success_does_not_promote_an_open_goal_or_a_definition(self):
        plan = {"goal": {"id": "SINGULAR_PREMISE_OBSTRUCT_R3", "name": "R3 obstruction", "domain": "R3",
                         "ci_mode": "foundation_audit", "root_status": "OPEN_NO_NATIVE_ROOT", "root_declaration": None,
                         "target_definition": "Example.target", "verification_scope": "Foundations only",
                         "open_obligations": ["Actual general-data construction"]},
                "source_revision": REVISION, "route": {}, "plan_sha256": "plan",
                "selected_packages": ["Root"], "selected_package_count": 1,
                "required_named_reports": 1, "orchestrator_sha256": "script",
                "audit_policy_sha256": "policy", "source_closure_sha256": "sources"}
        report = goal.base_report(plan)
        report["audit_status"] = "PASS"
        self.assertEqual(report["root_status"], "OPEN_NO_NATIVE_ROOT")
        self.assertEqual(report["ci_mode"], "foundation_audit")
        self.assertTrue(report["foundation_only"])
        self.assertIsNone(report["root_declaration"])
        self.assertFalse(report["target_definition_is_proof"])
        self.assertFalse(report["root_status_automatically_promoted"])
        self.assertFalse(report["full_project_acceptance"])

    def test_r3_foundations_keep_compatible_cache_donor_provenance_distinct(self):
        prior = "b" * 40
        plan = {"toolchain": "leanprover/lean4:v4.33.0", "mathlib_commit": "mathlib",
                "build_configuration": {}, "source_revision": REVISION,
                "route": {"event": "push", "upstream": {"run_id": "1234"}}}
        audit = {"status": "PASS", "audit_reused": False, "audit_origin_commit": prior,
                 "types": {"Example.theorem": "Example.theorem : True"},
                 "axioms": {"Example.theorem": []}, "declaration_count": 1}
        donor = {"status": "PASS", "repository": goal.REPOSITORY, "compiler_executed": True,
                 "all_endpoints_selected": True, "fresh_required_audits": True,
                 "source_pin_integrity": True, "commit": prior,
                 "toolchain": plan["toolchain"], "mathlib_commit": plan["mathlib_commit"],
                 "build_configuration": {}, "run_id": "5678",
                 "run_url": f"https://github.com/{goal.REPOSITORY}/actions/runs/5678",
                 "module_receipts": {"Example": {"status": "PASS"}},
                 "endpoints": [dict(audit, id="Example")], "cutout": dict(audit)}
        # Immutable exact caches may retain a prior full PASS donor.  Current
        # recursive source/object identities are checked by validate_receipts.
        goal.validate_donor(donor, plan)
        self.assertNotEqual(donor["commit"], plan["source_revision"])
        self.assertNotEqual(donor["run_id"], plan["route"]["upstream"]["run_id"])
        partial = copy.deepcopy(donor)
        partial["all_endpoints_selected"] = False
        with self.assertRaises(goal.ScopeError):
            goal.validate_donor(partial, plan)
        unapproved = copy.deepcopy(donor)
        unapproved["endpoints"][0]["axioms"]["Example.theorem"] = ["sorryAx"]
        with self.assertRaises(goal.ScopeError):
            goal.validate_donor(unapproved, plan)



if __name__ == "__main__":
    unittest.main()
