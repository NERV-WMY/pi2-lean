"""Check source fidelity, dependency pins, and the three final axiom lists."""

from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
record = json.loads((ROOT / "verification/source-hashes.json").read_text())
expected = {entry["path"] for entry in record["sources"]}
actual = {"Row12.lean"}
for namespace in ["Row12", "Row12EulerSupport", "Row12GaussGauge"]:
    actual.update(path.relative_to(ROOT).as_posix()
                  for path in (ROOT / namespace).rglob("*.lean"))
assert actual == expected, "Lean source inventory differs from the checked release."
for entry in record["sources"]:
    path = ROOT / entry["path"]
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == entry["sha256"], f"Source changed: {entry['path']}"
    source = path.read_text(encoding="utf-8-sig")
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), path
assert len(expected) == 69
assert (ROOT / "lean-toolchain").read_text().strip() == record["pins"]["lean"]
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib["type"] == "git"
assert mathlib["rev"] == record["pins"]["mathlib"]
assert all(p["type"] == "git" for p in manifest["packages"])

env = dict(os.environ)
env.pop("LEAN_PATH", None)
checked = subprocess.run(
    ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", "Row12.lean"],
    cwd=ROOT, env=env, text=True, encoding="utf-8",
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True,
)
print(checked.stdout, end="")
standard = {"propext", "Classical.choice", "Quot.sound"}
for name in ["Row12.row12_hasSum", "Row12.row12_summable", "Row12.row12_tsum"]:
    matches = re.findall(r"'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]",
                         checked.stdout)
    assert len(matches) == 1, f"Missing or duplicate axiom report: {name}"
    assert {x.strip() for x in matches[0].split(",")} == standard, name
print("PASS: 69 source hashes, pinned Git dependencies, no proof placeholders, and standard axioms only.")
