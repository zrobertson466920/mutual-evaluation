#!/usr/bin/env python3
"""Check computational annotation closure and axioms of the Public Lean interface.

The declaration inventory comes from Public source files, not a second statement
or prose baseline. Lean checks the compiled types and proofs. This inspection
checks project references in types and computational bodies, allowing internal
proof dependencies but not unannotated computational dependencies. Structure
constructor types are inspected too, so field types are included.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

spec = importlib.util.spec_from_file_location(
    "annotation_inventory", ROOT / "scripts/check_annotations.py")
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)

WALKER = r"""
open Lean Elab Command Meta

private partial def interfaceRefs (e : Expr) : MetaM NameSet := do
  if ← isProof e then
    return {}
  match e with
  | .const n _ => return ({} : NameSet).insert n
  | .app f a => return (← interfaceRefs f) ∪ (← interfaceRefs a)
  | .lam n t b bi | .forallE n t b bi =>
      let ts ← interfaceRefs t
      withLocalDecl n bi t fun x => do
        return ts ∪ (← interfaceRefs (b.instantiate1 x))
  | .letE n t v b _ =>
      let ts ← interfaceRefs t
      let vs ← interfaceRefs v
      withLetDecl n t v fun x => do
        return ts ∪ vs ∪ (← interfaceRefs (b.instantiate1 x))
  | .mdata _ b => interfaceRefs b
  | .proj n _ b => return (← interfaceRefs b).insert n
  | _ => return {}

private def interfaceProjectName (n : Name) : Bool :=
  n.toString.startsWith "MutualEvaluation." ||
    n.toString.startsWith "_private.MutualEvaluation."

private def interfaceAllowed (allowed : List Name) (n : Name) : MetaM Bool := do
  if allowed.contains n then
    return true
  -- Allow generated constructors/projections only through kernel metadata.
  match ← getConstInfo n with
  | .ctorInfo ctor => return allowed.contains ctor.induct
  | _ =>
      match ← getProjectionFnInfo? n with
      | some proj =>
          match ← getConstInfo proj.ctorName with
          | .ctorInfo ctor => return allowed.contains ctor.induct
          | _ => return false
      | none => return false

private def inspectInterface (allowed : List Name) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let refs ← interfaceRefs ci.type
  let refs ← if ci.isTheorem then pure refs else do
    match ci.value? with
    | some v => do
        let vr ← interfaceRefs v
        pure (refs ∪ vr)
    | none => pure refs
  let project := refs.toList.filter interfaceProjectName
  let mut missing : List Name := []
  for r in project do
    unless ← interfaceAllowed allowed r do
      missing := r :: missing
  logInfo m!"INTERFACE_REFS {n}: {project}"
  unless missing.isEmpty do
    throwError "Unannotated computational interface references in {n}: {missing}"
"""


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    selected = inventory.public_declarations()
    names = [name for items in selected.values() for _, name, _ in items]
    assert names and len(names) == len(set(names)), "Empty/duplicate Public inventory"
    validation = "import MutualEvaluation\n" + WALKER
    validation += "\nrun_cmd do\n"
    validation += "  let selected : List Name := [" + ", ".join(
        "``" + name for name in names) + "]\n"
    validation += r"""
  for n in selected do
    liftTermElabM <| inspectInterface selected n
    match ← getConstInfo n with
    | .inductInfo info =>
        for ctor in info.ctors do
          liftTermElabM <| inspectInterface selected ctor
    | _ => pure ()
  logInfo m!"INTERFACE_CLOSURE_OK {selected.length}"
"""
    validation += "\n".join("#print axioms " + name for name in names) + "\n"
    outdir = ROOT / ".verification"
    outdir.mkdir(exist_ok=True)
    receipt_path = outdir / "interface-receipt.json"
    # A failed run must not leave an older success receipt at this path.
    if receipt_path.exists():
        receipt_path.unlink()
    (outdir / "interface-validation.lean.txt").write_text(validation)
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env.get("PATH", "")
    print(f"Checking {len(names)} Public declarations and structure field types", flush=True)
    with tempfile.TemporaryDirectory(prefix="mutual-evaluation-interface-") as tmp:
        path = Path(tmp) / "InterfaceCheck.lean"
        path.write_text(validation)
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", str(path)],
            cwd=ROOT, env=env, text=True, capture_output=True, timeout=240)
    output = result.stdout + result.stderr
    (outdir / "interface-validation.log").write_text(output)
    if result.returncode:
        print(output[-20000:], flush=True)
        raise SystemExit(result.returncode)
    reports = list(re.finditer(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        output, re.M))
    axioms = {a.strip() for m in reports
              for a in (m.group(2) or "").split(",") if a.strip()}
    assert [m.group(1) for m in reports] == names, "Missing/misordered axiom reports"
    assert axioms <= ALLOWED_AXIOMS, axioms
    assert f"INTERFACE_CLOSURE_OK {len(names)}" in output
    sources = [ROOT / "MutualEvaluation.lean"] + sorted(
        (ROOT / "MutualEvaluation").rglob("*.lean"))
    receipt = {
        "scope": "Public source interface: computational annotation closure and axioms",
        "declarations": names,
        "structure_field_types_checked": True,
        "checker_sha256": digest(Path(__file__)),
        "inventory_checker_sha256": digest(ROOT / "scripts/check_annotations.py"),
        "source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in sources},
        "axioms": sorted(axioms),
        "inspection_exit": result.returncode,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS Public computational annotation closure, including structure field types",
          flush=True)
    print("PASS", len(reports), "recursive-axiom reports:", sorted(axioms), flush=True)


if __name__ == "__main__":
    main()