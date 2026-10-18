#!/usr/bin/env python3
"""One entry point for every local check of this repository.

    python scripts/verify.py [--fetch-cache] [--skip-build]

In order: the pins (lean-toolchain and the Mathlib revision of lake-manifest.json are the committed
ones), the source guard and its subprocess controls for prohibited Lake options, the definition
comparison between Challenge.lean and GrahamLPT/Defs.lean, the
statement comparison between Challenge.lean and Solution.lean, the standard-library replay
scripts/check_lpt.py (the bounds, the key lemma and both families, under -I and under -O -I), the metadata (formalization.yaml parses;
its title length, main results and alignment against comparator.json, every alignment status proved; no
definition holes; no original-proof source), the Lean build of every target (including the Test audit, which fails on
any axiom beyond propext, Classical.choice and Quot.sound), the module-resolution check, the
elaboration checks of the compared definitions and of every constant named under them (printed with
pp.all from the Challenge and from GrahamLPT.Defs; a module-private auxiliary would differ) and of the
compared theorems' types (from the Challenge and from the Solution), which must
agree exactly as the registry's comparator demands, and Palomar's
core-notation audit of the compared declarations. The compared definitions are read from
Challenge.lean at run time: every `def`, `noncomputable def` and `abbrev` at the start of a line, in namespace
GrahamLPT. `--fetch-cache` runs
`lake exe cache get` first (network); `--skip-build` leaves out the four Lean steps. The last line
is `VERIFY: PASS` or `VERIFY: FAIL` for a full run, and `VERIFY (source/replay only): PASS` or
`VERIFY (source/replay only): FAIL` when Lean checks were skipped. Exit status 0 on PASS only.
"""

from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
TARGETS = ["GrahamLPT", "Challenge", "Solution", "Test"]
NAMESPACE = "GrahamLPT"
DEF_HEAD = re.compile(r"^(?:noncomputable )?(?:def|abbrev) ([\w.']+)", flags=re.M)


def definitions():
    """Every definition of Challenge.lean, fully qualified. They are fully specified in the Challenge,
    so comparator.json lists none of them in definition_names (a name there is a definition HOLE
    whose value the Solution supplies); the elaboration check and the notation audit cover them all."""
    text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    return [f"{NAMESPACE}.{name}" for name in DEF_HEAD.findall(text)]


def run(args, **kw):
    print("+", " ".join(args), flush=True)
    return subprocess.run(args, cwd=ROOT, text=True, encoding="utf-8", errors="replace", **kw)


def step(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""), flush=True)
    return ok


def check_pins():
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    revs = {p["name"]: p.get("rev") for p in manifest.get("packages", [])}
    ok = toolchain == TOOLCHAIN and revs.get("mathlib") == MATHLIB_REV
    return step("pins", ok, f"toolchain {toolchain}, mathlib {revs.get('mathlib')}")


def check_script(name, args):
    result = run([sys.executable] + args, capture_output=True)
    tail = (result.stdout + result.stderr).strip().splitlines()[-1:] or [""]
    return step(name, result.returncode == 0, tail[0])


def check_replay():
    ok = True
    for flags in (["-I"], ["-O", "-I"]):
        result = run([sys.executable] + flags + ["scripts/check_lpt.py"], capture_output=True)
        lines = result.stdout.strip().splitlines()
        good = result.returncode == 0 and lines[-1:] == ["VERDICT: PASS"]
        ok &= step(f"check_lpt.py (the standard-library replay under {' '.join(flags)})", good,
                   lines[-1] if lines else (result.stderr.strip().splitlines()[-1:] or [""])[0])
    return ok


def check_yaml():
    """formalization.yaml parses; its title is within the registry's limit; its main_results match
    comparator.json; its alignment lists the compared theorems in comparator.json's order with every status
    proved; comparator.json lists no definition holes; no source has type or relationship original-proof."""
    path = ROOT / "formalization.yaml"
    if not path.exists():
        return step("formalization.yaml", False, "missing")
    try:
        import yaml
    except ImportError:
        return step("formalization.yaml", False, "PyYAML is not installed (pip install pyyaml)")
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
        config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
        problems = []
        title = data["project"]["name"]
        if len(title) > 300:
            problems.append(f"title has {len(title)} characters (limit 300)")
        if not data["project"].get("responsible_maintainers"):
            problems.append("project.responsible_maintainers is empty (the registry's contract requires a nonempty list)")
        mains = [m["declaration"] for m in data["status"]["main_results"]]
        if mains != config["theorem_names"]:
            problems.append("status.main_results differ from comparator.json theorem_names")
        aligned = [a["lean"] for a in data.get("alignment", {}).get("statements", [])]
        if aligned != config["theorem_names"]:
            problems.append("alignment.statements differ from comparator.json theorem_names in order")
        statuses = {a.get("status") for a in data.get("alignment", {}).get("statements", [])}
        if statuses != {"proved"}:
            problems.append(f"alignment statuses other than proved: {sorted(statuses - {'proved'})}")
        if config.get("definition_names"):
            problems.append("comparator.json lists definition holes; this entry's definitions are "
                            "fully specified")
        if any("original-proof" in (src.get("type"), src.get("relationship")) for src in data.get("sources", [])):
            problems.append("an original-proof source would force other/background on every other "
                            "source")
    except (KeyError, TypeError, ValueError) as error:
        return step("formalization.yaml", False, f"malformed: {error!r}")
    schema = ROOT / "scripts" / "formalization.schema.json"
    if schema.exists():
        try:
            import jsonschema
            jsonschema.validate(data, json.loads(schema.read_text(encoding="utf-8")))
        except ImportError:
            problems.append("jsonschema is not installed; schema not validated")
        except Exception as error:  # the validator's first line is the message
            problems.append("schema: " + str(error).splitlines()[0])
    detail = "; ".join(problems) if problems else (
        f"parses; title {len(title)} chars; {len(mains)} main results; "
        f"{len(data.get('sources', []))} sources" + ("; schema valid" if schema.exists() else ""))
    return step("formalization.yaml", not problems, detail)


def check_build():
    ok = True
    for target in TARGETS:
        result = run(["lake", "build", target], capture_output=True)
        output = result.stdout + result.stderr
        bad = [line for line in output.splitlines() if "error" in line.lower()]
        detail = bad[0] if bad else (
            "built" if result.returncode == 0 else f"exited with status {result.returncode}")
        if target == "Test" and result.returncode == 0:
            audit = re.search(r"Audited \d+ project constants; unexpected axiom dependencies: \d+\.",
                              output)
            if audit:
                detail += "; " + audit.group()
        ok &= step(f"lake build {target}", result.returncode == 0 and not bad,
                   detail)
    return ok


def check_module_resolution():
    result = run(["lake", "env", sys.executable, "scripts/check_module_resolution.py"],
                 capture_output=True)
    text = (result.stdout + result.stderr).strip()
    return step("module resolution", result.returncode == 0, text.splitlines()[-1] if text else "")


def check_definition_elaboration(names):
    """The compared definitions, printed with pp.all from the Challenge and from the development's
    definitions module, must agree exactly: the comparator judges the elaborated constants, which
    depend on the imports through instance resolution."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    outputs = []
    for module in (config["challenge_module"], f"{NAMESPACE}.Defs"):
        path = scratch / f"verify_pp_{module.replace('.', '_')}.lean"
        header = "import " + module + "\nset_option pp.all true\n"
        path.write_text(header + "".join("#print " + n + "\n" for n in names), encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)], capture_output=True)
        outputs.append((result.returncode, result.stdout))
        path.unlink()
    ok = all(rc == 0 for rc, _ in outputs) and outputs[0][1].strip() != "" and \
        outputs[0][1] == outputs[1][1]
    return step(f"definition elaboration (Challenge vs {NAMESPACE}.Defs, pp.all, {len(names)} names)",
                ok, "identical" if ok else "the printed terms differ or a print failed")

AUX_PROBE = """import {module}
set_option pp.all true
set_option pp.proofs true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let defs : List Name := [{names}]
  let mut found : Array Name := #[]
  for (n, _) in env.constants.toList do
    let user := (privateToUserName? n).getD n
    if defs.any (fun d => d.isPrefixOf user) then found := found.push n
  let sorted := found.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    let some ci := env.find? n | continue
    let val := match ci.value? with | some v => m!"{{v}}" | none => m!"<none>"
    logInfo m!"{{n}} : {{ci.type}} := {{val}}"
"""


def check_auxiliary_elaboration(names):
    """Every constant of the environment named under a compared definition (the definition itself and
    the auxiliary `_proof_n` theorems Lean abstracts from the proofs inside its body), printed with
    pp.all and pp.proofs from the Challenge and from the development's definitions module, must agree
    exactly. The registry's comparator compares the auxiliary constants too, and an auxiliary theorem
    that is private to its module carries the module name (`_private.Challenge.0...` against
    `_private.GrahamLPT.Defs.0...`), so the two prints differ wherever one exists: `omega` inside a
    definition's body produced one (the comparator's rejection of 2026-10-18); explicit terms do not."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    outputs = []
    for module in (config["challenge_module"], f"{NAMESPACE}.Defs"):
        path = scratch / f"verify_aux_{module.replace('.', '_')}.lean"
        path.write_text(AUX_PROBE.format(module=module, names=", ".join("``" + n for n in names)),
                        encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)], capture_output=True)
        body = "\n".join(line.split(": info: ", 1)[-1] for line in result.stdout.splitlines())
        outputs.append((result.returncode, body))
        path.unlink()
    constants = sum(1 for line in outputs[0][1].splitlines() if " := " in line)
    ok = all(rc == 0 for rc, _ in outputs) and constants >= len(names) and \
        outputs[0][1] == outputs[1][1] and "_private." not in outputs[0][1]
    return step(f"auxiliary-constant elaboration (Challenge vs {NAMESPACE}.Defs, pp.all, "
                f"{len(names)} definitions)", ok,
                f"identical, {constants} constants, none private" if ok
                else "the printed constants differ, one is private, or a print failed")


def check_theorem_elaboration():
    """The compared theorems, printed (#check with pp.all) from the Challenge and from the Solution, must agree
    exactly: the text comparison of the headers is not enough, the comparator judges the elaborated types."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    theorems = config["theorem_names"]
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    outputs = []
    for module in (config["challenge_module"], config["solution_module"]):
        path = scratch / f"verify_check_{module}.lean"
        header = "import " + module + "\nset_option pp.all true\n"
        path.write_text(header + "".join("#check @" + n + "\n" for n in theorems), encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)], capture_output=True)
        outputs.append((result.returncode, result.stdout))
        path.unlink()
    ok = all(rc == 0 for rc, _ in outputs) and outputs[0][1].strip() != "" and \
        outputs[0][1] == outputs[1][1] and outputs[0][1].count("\n") >= len(theorems)
    return step(f"theorem elaboration (Challenge vs Solution, pp.all, {len(theorems)} names)",
                ok, "identical" if ok else "the printed types differ or a check failed")


def check_notation_audit(names):
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    args = ["lake", "env", "lean", "--run", "scripts/core_notation_audit.lean",
            config["challenge_module"]]
    for name in config["theorem_names"]:
        args += ["theorem", name]
    for name in names:
        args += ["def", name]
    result = run(args, capture_output=True)
    try:
        rows = json.loads(result.stdout)
    except ValueError:
        rows = []
    expected = len(config["theorem_names"]) + len(names)
    printed = {row.get("name") for row in rows} if isinstance(rows, list) else set()
    ok = result.returncode == 0 and len(printed) == expected and \
        printed == set(config["theorem_names"]) | set(names)
    return step("core-notation audit", ok, f"{len(printed)} of {expected} declarations printed")


def main():
    fetch = "--fetch-cache" in sys.argv
    skip_build = "--skip-build" in sys.argv
    names = definitions()
    ok = step("compared definitions read from Challenge.lean", len(names) > 0,
              f"{len(names)} names")
    ok &= check_pins()
    ok &= check_script("source guard", ["scripts/check-source.py"])
    ok &= check_script("source guard controls", ["scripts/check_source_guard.py"])
    ok &= check_script("definitions", ["scripts/check_definitions.py"])
    ok &= check_script("statements", ["scripts/check_statements.py"])
    ok &= check_replay()
    ok &= check_yaml()
    if not skip_build:
        if fetch:
            ok &= step("lake exe cache get", run(["lake", "exe", "cache", "get"]).returncode == 0)
        ok &= check_build()
        ok &= check_module_resolution()
        ok &= check_definition_elaboration(names)
        ok &= check_auxiliary_elaboration(names)
        ok &= check_theorem_elaboration()
        ok &= check_notation_audit(names)
    else:
        print("[SKIP] Lean build and axiom audit; module resolution; definition and auxiliary-constant "
              "elaboration; core-notation audit", flush=True)
    scope = "VERIFY (source/replay only)" if skip_build else "VERIFY"
    print(f"{scope}: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
