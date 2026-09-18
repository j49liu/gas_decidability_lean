#!/usr/bin/env python3
"""Check the public HGAS import closure and outside-module catalog.

The script follows project imports starting at ``HGAS.lean``, counts source
files under ``HGAS/``, and checks that ``LEGACY_MODULES.md`` lists exactly
the modules outside the public closure.
"""

from __future__ import annotations

import re
from pathlib import Path


LEAN_ROOT = Path(__file__).resolve().parents[1]
HGAS_ROOT = LEAN_ROOT / "HGAS"
PUBLIC_ROOT = LEAN_ROOT / "HGAS.lean"
CATALOG = LEAN_ROOT / "LEGACY_MODULES.md"

EXPECTED_TOTAL = 824
EXPECTED_PUBLIC = 783
EXPECTED_OUTSIDE = 41

IMPORT_RE = re.compile(r"^import\s+(HGAS(?:\.[A-Za-z0-9_']+)*)\s*$")
CATALOG_RE = re.compile(r"^\d+\.\s+`(HGAS/.*\.lean)`$")


def module_path(module: str) -> Path:
    if module == "HGAS":
        return PUBLIC_ROOT
    return LEAN_ROOT / (module.replace(".", "/") + ".lean")


def project_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.fullmatch(line)
        if match is not None:
            imports.append(match.group(1))
    return imports


def source_module(path: Path) -> str:
    relative = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(relative.parts)


def main() -> None:
    sources = sorted(HGAS_ROOT.rglob("*.lean"))
    all_modules = {source_module(path) for path in sources}

    closure: set[str] = set()
    pending = ["HGAS"]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        path = module_path(module)
        if not path.is_file():
            raise SystemExit(f"missing project import: {module} ({path})")
        closure.add(module)
        pending.extend(project_imports(path))

    public_modules = (closure - {"HGAS"}) & all_modules
    outside_modules = all_modules - public_modules
    outside_paths = {
        module.replace(".", "/") + ".lean" for module in outside_modules
    }

    catalog_paths = {
        match.group(1)
        for line in CATALOG.read_text(encoding="utf-8").splitlines()
        if (match := CATALOG_RE.fullmatch(line)) is not None
    }

    print(f"HGAS source modules: {len(all_modules)}")
    print(f"Public import closure: {len(public_modules)}")
    print(f"Outside public closure: {len(outside_modules)}")

    expected_counts = (
        ("source modules", EXPECTED_TOTAL, len(all_modules)),
        ("public modules", EXPECTED_PUBLIC, len(public_modules)),
        ("outside modules", EXPECTED_OUTSIDE, len(outside_modules)),
    )
    for label, expected, actual in expected_counts:
        if actual != expected:
            raise SystemExit(f"expected {expected} {label}, found {actual}")

    missing = sorted(outside_paths - catalog_paths)
    extra = sorted(catalog_paths - outside_paths)
    if missing or extra:
        if missing:
            print("Missing from LEGACY_MODULES.md:")
            print(*missing, sep="\n")
        if extra:
            print("Listed but not outside the public closure:")
            print(*extra, sep="\n")
        raise SystemExit("outside-module catalog mismatch")

    print("LEGACY_MODULES.md exact-set check: PASS")


if __name__ == "__main__":
    main()
