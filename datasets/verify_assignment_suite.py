#!/usr/bin/env python3
"""Verify assignment_suite.txt matches assignment_suite.manifest.json."""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "assignment_suite.manifest.json"
TXT = ROOT / "assignment_suite.txt"


def _read_txt_goals(path: Path) -> list[str]:
    goals: list[str] = []
    with path.open(encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            goals.append(s)
    return goals


def main() -> int:
    if not MANIFEST.exists() or not TXT.exists():
        print("Missing assignment_suite files.", file=sys.stderr)
        return 1

    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    manifest_goals = [g["goal"] for g in data.get("goals", [])]
    txt_goals = _read_txt_goals(TXT)

    if manifest_goals != txt_goals:
        print("Mismatch between manifest and txt:", file=sys.stderr)
        print(f"  manifest: {len(manifest_goals)} goals", file=sys.stderr)
        print(f"  txt:      {len(txt_goals)} goals", file=sys.stderr)
        for i, (m, t) in enumerate(zip(manifest_goals, txt_goals)):
            if m != t:
                print(f"  first diff at index {i}:", file=sys.stderr)
                print(f"    manifest: {m!r}", file=sys.stderr)
                print(f"    txt:      {t!r}", file=sys.stderr)
                break
        if len(manifest_goals) != len(txt_goals):
            print("  (length differs)", file=sys.stderr)
        return 1

    stats = data.get("stats", {})
    tiers = [g.get("tier") for g in data.get("goals", [])]
    for tier in ("easy", "medium", "hard"):
        expected = stats.get(tier)
        actual = tiers.count(tier)
        if expected is not None and expected != actual:
            print(f"Tier count mismatch for {tier}: expected {expected}, got {actual}", file=sys.stderr)
            return 1

    print(f"OK: {len(txt_goals)} goals synced (easy={tiers.count('easy')}, "
          f"medium={tiers.count('medium')}, hard={tiers.count('hard')})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
