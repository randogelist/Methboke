"""One explicit, receipt-by-receipt migration of the pre-WFB native context.

This adapter does not trust a cache label or erase driver/policy hashes. It
reconstructs the old identity using the exact reviewed legacy configuration,
then checks the current bytes of every source and imported object recursively.
Only unchanged legacy modules can acquire the new context identity. The new
run still executes all endpoint/type/axiom audits before it can be accepted.
"""
from __future__ import annotations

import copy
from pathlib import Path

import build

ADAPTER_VERSION = "wfb-owned-sources-v1"
LEGACY_SOURCE_COMMIT = "43530b70d044624cbf83a3480840187a567549a5"
LEGACY_CONFIGURATION = {
    "lean-toolchain": "302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b",
    "lake-manifest.json": "5ad4bb9f8a90899eff0dccf7bae5eb9fbef3f1f3822f6e1759f1118f5bef6215",
    "lakefile.lean": "9e577cb61d3538df3726d10ad385a658ddb4dfa696fed5f19f7861795c32c3dd",
    "ci/build.py": "d22455bb6a2a34cc3aaa577d29b91c0a66dac815bd4ecebd71cbce3205ebb604",
}
LEGACY_DRIVER = "f382002a86cf963ad3f6e44022196357b794d175242242a297e56f8e201caf47"
LEGACY_LAUNCHER = "0f916f63a4b400175b3dfc58a13728299c5daafddf71cca0f8ac40bcbf686a57"
LEGACY_ENDPOINTS = frozenset({
    "Galerkin", "MathlibAnalytic", "MathlibFourier", "MathlibODE", "PhysicalNSE",
    "QFBCutoff", "QFBLerayHopf", "QFBRestart", "QFBRoot", "QFBTail",
    "QFBTraceUniqueness", "RelativeEnergy", "SerrinComparison", "SmallH12",
})


def module_identity(context, name, record, dependencies):
    return build.fingerprint({"context": context, "source": record["sha256"],
        "module": name, "imports": {i: {"identity": r["identity"], "objects": r["object_files"]}
                                     for i, r in dependencies.items()}})


def legacy_context(previous, current):
    """None means there is no approved semantic-context migration."""
    if (previous.get("status") != "PASS" or previous.get("compiler_executed") is not True
            or previous.get("all_endpoints_selected") is not True
            or previous.get("fresh_required_audits") is not True
            or previous.get("build_configuration") != LEGACY_CONFIGURATION
            or current.get("launcher_policy") != LEGACY_LAUNCHER
            or previous.get("compiler") != current.get("compiler")
            or previous.get("external_objects") != current.get("external_objects")
            or previous.get("platform") != current.get("platform")):
        return None
    if any(current.get("configuration", {}).get(key) != value
           for key, value in LEGACY_CONFIGURATION.items() if key != "ci/build.py"):
        return None
    if current.get("lock") != LEGACY_CONFIGURATION["lake-manifest.json"]:
        return None
    endpoints = previous.get("endpoints", [])
    if (len(endpoints) != len(LEGACY_ENDPOINTS)
            or {e.get("id") for e in endpoints} != LEGACY_ENDPOINTS
            or any(e.get("status") != "PASS" or e.get("audit_reused") is not False
                   for e in endpoints)
            or previous.get("cutout", {}).get("status") != "PASS"
            or previous.get("cutout", {}).get("audit_reused") is not False):
        return None
    return {"compiler": current["compiler"], "lock": current["lock"],
        "configuration": copy.deepcopy(LEGACY_CONFIGURATION), "driver": LEGACY_DRIVER,
        "launcher_policy": LEGACY_LAUNCHER, "external_objects": current["external_objects"],
        "platform": current["platform"]}


def migrate(previous, current, records, output, receipt_matches):
    """Return an in-memory candidate receipt map; never modify the passed cache."""
    old = previous.get("module_receipts", {}) if previous.get("status") == "PASS" else {}
    metadata = {"adapter": ADAPTER_VERSION, "legacy_source_commit": LEGACY_SOURCE_COMMIT,
                "migrated_count": 0, "rejected_count": 0, "status": "NOT_APPLICABLE"}
    legacy = legacy_context(previous, current)
    if legacy is None:
        return old, metadata
    metadata["status"] = "EXACT_LEGACY_CONTEXT_RECONSTRUCTION"
    pending, verified, migrated = set(records), {}, {}
    while pending:
        ready = sorted(name for name in pending
                       if not any(imp in pending for imp in records[name]["imports"]))
        if not ready:
            raise build.BuildError("cyclic graph during legacy receipt reconstruction")
        for name in ready:
            pending.remove(name)
            dependencies = [imp for imp in records[name]["imports"] if imp in records]
            if any(imp not in verified for imp in dependencies):
                continue
            legacy_dependencies = {imp: verified[imp] for imp in dependencies}
            original_identity = module_identity(legacy, name, records[name], legacy_dependencies)
            artifact = Path(output).joinpath(*name.split(".")).with_suffix(".olean")
            receipt = old.get(name)
            if (not isinstance(receipt, dict) or receipt.get("status") != "PASS"
                    or not receipt_matches(receipt, original_identity, artifact)):
                continue
            verified[name] = receipt
            replacement = copy.deepcopy(receipt)
            replacement["identity"] = module_identity(current, name, records[name],
                {imp: migrated[imp] for imp in dependencies})
            replacement["context_migration"] = {"adapter": ADAPTER_VERSION,
                                                 "legacy_identity": original_identity}
            migrated[name] = replacement
    metadata["migrated_count"] = len(migrated)
    metadata["rejected_count"] = len(set(old) & set(records)) - len(migrated)
    # Unmigrated entries retain their old identities and therefore cannot pass
    # the normal new-context receipt check. No unknown object is certified here.
    return {**old, **migrated}, metadata
