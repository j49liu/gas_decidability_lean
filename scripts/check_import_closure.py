#!/usr/bin/env python3
"""Check both public import closures and the HGAS outside-module catalog.

The preserved HGAS checks require the 837/796/41 counts and exact equality
with ``LEGACY_MODULES.md``. The Stability check requires every source module
under ``Stability/`` to belong to the ``Stability.lean`` closure. Catalogued
HGAS modules used by Stability are reported separately.
"""

from __future__ import annotations

import re
from pathlib import Path


LEAN_ROOT = Path(__file__).resolve().parents[1]
HGAS_ROOT = LEAN_ROOT / "HGAS"
STABILITY_ROOT = LEAN_ROOT / "Stability"
CATALOG = LEAN_ROOT / "LEGACY_MODULES.md"

EXPECTED_TOTAL = 837
EXPECTED_PUBLIC = 796
EXPECTED_OUTSIDE = 41

IMPORT_RE = re.compile(r"^import\s+((?:HGAS|Stability)(?:\.[A-Za-z0-9_']+)*)\s*$")
CATALOG_RE = re.compile(r"^\d+\.\s+`(HGAS/.*\.lean)`$")


def module_path(module: str) -> Path:
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


def import_closure(root: str) -> set[str]:
    closure: set[str] = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        path = module_path(module)
        if not path.is_file():
            raise SystemExit(f"missing project import: {module} ({path})")
        closure.add(module)
        pending.extend(project_imports(path))
    return closure


def main() -> None:
    sources = sorted(HGAS_ROOT.rglob("*.lean"))
    all_modules = {source_module(path) for path in sources}
    closure = import_closure("HGAS")

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

    stability_modules = {
        source_module(path) for path in STABILITY_ROOT.rglob("*.lean")
    }
    stability_closure = import_closure("Stability")
    stability_public = stability_closure & stability_modules
    stability_outside = stability_modules - stability_public
    print(f"Stability source modules: {len(stability_modules)}")
    print(f"Stability modules in Stability.lean closure: {len(stability_public)}")
    print(f"Stability modules outside Stability.lean closure: {len(stability_outside)}")
    if stability_outside:
        print(*sorted(stability_outside), sep="\n")
        raise SystemExit("Stability modules outside the public closure")

    shared_legacy = outside_modules & stability_closure
    print(f"Catalogued HGAS modules in Stability.lean closure: {len(shared_legacy)}")
    for module in sorted(shared_legacy):
        print(f"  {module.replace('.', '/')}.lean")
    print("Stability import-closure check: PASS")


if __name__ == "__main__":
    main()
