#!/usr/bin/env python3
"""Count tracked Lean source text and keep the README statistic reproducible.

This script uses only Python's standard library and read-only Git commands.
It never invokes Lean, Lake, a compiler, or the existing verification scripts.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
START = "<!-- lean-source-stats:start -->"
END = "<!-- lean-source-stats:end -->"
WORKFLOW = "https://github.com/randogelist/Methboke/actions/workflows/lean-line-count.yml"


def git(*args):
    return subprocess.check_output(
        ["git", "-c", "core.fsmonitor=false", "-C", str(ROOT), *args]
    )


def collect():
    paths = sorted(
        entry.decode("utf-8")
        for entry in git("ls-files", "-z", "--", "*.lean").split(b"\0")
        if entry
    )
    totals = {
        name: {"files": 0, "lines": 0}
        for name in ("non_vendored", "vendored", "archives", "project", "repository")
    }
    files = []
    for relative in paths:
        path = ROOT / relative
        if path.is_symlink() or not path.is_file():
            raise ValueError("Expected a regular tracked Lean file: " + relative)
        data = path.read_bytes()
        lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
        if relative.startswith("Temp-folder/"):
            category = "archives"
        elif relative.startswith("Material/_vendor/"):
            category = "vendored"
        else:
            category = "non_vendored"
        scopes = [category, "repository"]
        if category != "archives":
            scopes.append("project")
        for scope in scopes:
            totals[scope]["files"] += 1
            totals[scope]["lines"] += lines
        files.append({"path": relative, "category": category, "lines": lines})
    return {
        "schema_version": 1,
        "source_commit": git("rev-parse", "HEAD").decode("ascii").strip(),
        "metric": "Physical LF-delimited lines, including comments and blank lines",
        "selection": "Git-tracked filenames ending in .lean",
        "archive_prefix": "Temp-folder/",
        "vendor_prefix": "Material/_vendor/",
        "totals": totals,
        "files": files,
    }


def render(report):
    totals = report["totals"]
    project = totals["project"]
    rows = [
        START,
        "## Lean source size",
        "",
        "[![Lean source count](" + WORKFLOW + "/badge.svg?branch=main)](" + WORKFLOW + ")",
        "",
        "**{lines:,} physical lines of Lean across {files:,} tracked .lean files** "
        "in the project tree, excluding archive/reference copies in Temp-folder/.".format(
            **project
        ),
        "",
        "| Scope | Lean files | Physical lines |",
        "|---|---:|---:|",
    ]
    for label, scope in (
        ("Non-vendored project files", "non_vendored"),
        ("Retained vendored sources ([Material/_vendor/](Material/_vendor/))", "vendored"),
        ("**Project tree total**", "project"),
        ("Archive/reference copies ([Temp-folder/](Temp-folder/))", "archives"),
        ("All tracked .lean files, including archive/reference copies", "repository"),
    ):
        value = totals[scope]
        rows.append("| {} | {:,} | {:,} |".format(label, value["files"], value["lines"]))
    rows.extend(
        [
            "",
            "These are physical source lines, including comments, blank lines, audit "
            "consumers, and Lean build-description files. They are not an authorship "
            "or compiled-module count. Only Git-tracked filenames ending in .lean "
            "are counted; compressed archives and .lean.txt documents are not unpacked "
            "or counted.",
            "",
            "[Lean source count CI](" + WORKFLOW + ") recounts the files and checks this "
            "section using Python and Git only. Its JSON artifact includes the exact "
            "source commit and every counted file.",
            "",
            "After staging source-file additions or deletions, refresh this section with:",
            "",
            "    python3 scripts/count_lean_lines.py --write-readme",
            END,
        ]
    )
    return "\n".join(rows)


def replace_section(text, block):
    if text.count(START) != 1 or text.count(END) != 1:
        raise ValueError("README must contain exactly one Lean source statistics marker pair")
    start, end = text.index(START), text.index(END)
    if end < start:
        raise ValueError("README Lean source statistics markers are reversed")
    return text[:start] + block + text[end + len(END):]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check-readme", action="store_true")
    mode.add_argument("--write-readme", action="store_true")
    parser.add_argument("--readme", type=Path, default=ROOT / "README.md")
    parser.add_argument("--output", type=Path, help="Write the full JSON file inventory")
    parser.add_argument("--summary", type=Path, help="Append a Markdown CI job summary")
    args = parser.parse_args()
    report = collect()
    block = render(report)
    print(block)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as summary:
            summary.write("Source commit: " + report["source_commit"] + "\n\n" + block + "\n")
    if args.check_readme or args.write_readme:
        original = args.readme.read_bytes().decode("utf-8")
        updated = replace_section(original, block)
        if args.write_readme:
            if updated != original:
                args.readme.write_bytes(updated.encode("utf-8"))
        elif updated != original:
            print(
                "README Lean source statistics are stale. Run: "
                "python3 scripts/count_lean_lines.py --write-readme",
                file=sys.stderr,
            )
            return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print("Lean source count failed: " + str(error), file=sys.stderr)
        sys.exit(1)
