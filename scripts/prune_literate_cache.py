#!/usr/bin/env python3
"""Remove cached literate pages for deleted repository modules before rendering HTML."""

import argparse
from pathlib import Path


LIBRARIES = ("FormalConjectures", "FormalConjecturesForMathlib", "FormalConjecturesUtil")


def prune(source_root: Path, literate_root: Path) -> list[Path]:
    """Remove orphan module JSON and its Lake sidecars, retaining live module caches."""
    # A wrong source root must not turn every cache entry into an orphan.
    if not all((source_root / library).is_dir() for library in LIBRARIES):
        raise ValueError(f"Not a Formal Conjectures source root: {source_root}")

    removed = []
    for page in sorted(literate_root.rglob("*.json")):
        relative = page.relative_to(literate_root)
        if relative.parts[0] not in LIBRARIES and relative.as_posix() not in {
            f"{library}.json" for library in LIBRARIES
        }:
            continue
        if (source_root / relative.with_suffix(".lean")).is_file():
            continue
        page.unlink()
        for suffix in (".hash", ".trace"):
            page.with_name(page.name + suffix).unlink(missing_ok=True)
        removed.append(relative)
    return removed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_root", type=Path)
    parser.add_argument("literate_root", type=Path)
    args = parser.parse_args()
    try:
        removed = prune(args.source_root, args.literate_root)
    except ValueError as error:
        parser.error(str(error))
    for page in removed:
        print(f"Removed stale literate page: {page}")
    print(f"Removed {len(removed)} stale literate page(s).")


if __name__ == "__main__":
    main()
