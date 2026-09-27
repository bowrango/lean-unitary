"""Evaluator for lean-unitary.

Scores a formally verified n-qubit unitary synthesis algorithm by the CNOT bound it *proves*,
relative to the Shende-Markov-Bullock lower bound ceil((4^n - 3n - 1) / 4), for n = 3..8.

The climber can read this file. There is no hidden data: the task is to prove theorems, and
the evaluator's job is to make sure the proofs are real. Everything it trusts is frozen in
lean/ next to this file:

  lean/Spec.lean        the statement being proved (overwrites the submission's copy)
  lean/Checker.lean     kernel re-check of the submission + claim/axiom verification
  lean/lakefile.toml    build config and dependency pins (the submission's copies are ignored)
  lean/lake-manifest.json
  lean/lean-toolchain
"""

import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

HILL = Path(__file__).resolve().parent
FROZEN = HILL / "lean"
BUILD_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")

# Qubit counts scored, and the Shende-Markov-Bullock lower bound for each.
QUBITS = range(3, 9)
LOWER_BOUND = {n: -(-(4**n - 3 * n - 1) // 4) for n in QUBITS}  # 14, 61, 252, 1020, 4091, 16378
CHECKER_ARGS = ["general", *map(str, QUBITS)]

BUILD_TIMEOUT_S = 2400
CHECK_TIMEOUT_S = 900
LOG_TAIL_LINES = 60

# Constructs banned from submission sources. The kernel re-check already makes proofs
# trustworthy; these close the remaining routes: extra axioms, compiler-trusting decision
# procedures, and running arbitrary code while the evaluator builds the submission.
FORBIDDEN = [
    (r"\baxiom\b", "`axiom` declarations"),
    (r"\bnative_decide\b", "`native_decide` (trusts the compiler)"),
    (r"\bofReduceBool\b", "`Lean.ofReduceBool` (trusts the compiler)"),
    (r"\bimplemented_by\b|\bextern\b|\bcsimp\b", "compiler attributes"),
    (r"\bunsafe\b", "`unsafe` code"),
    (r"#eval\b|\brun_cmd\b|\brun_elab\b|\brun_meta\b|\brun_tac\b", "running code at build time"),
    (r"\b(builtin_)?initialize\b", "initializers"),
    (r"\b(macro|macro_rules|elab|elab_rules|syntax|declare_syntax_cat)\b", "syntax extensions"),
    (r"@\[[^\]]*\b(command_elab|term_elab|tactic|init|env_linter)\b", "elaborator attributes"),
    (r"\bdebug\.skipKernelTC\b", "disabling the kernel"),
]


def _fail(error: str, **details) -> dict:
    return {
        "passed": False,
        "metrics": [],
        "config": [],
        "details": {"error": error, **details},
    }


def _strip_comments(src: str) -> str:
    """Remove `--` line comments and (nested) `/- -/` block comments."""
    out, i, depth = [], 0, 0
    while i < len(src):
        two = src[i : i + 2]
        if two == "/-":
            depth, i = depth + 1, i + 2
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def _submission_sources(submission: Path) -> list[Path]:
    root = submission / "LeanUnitary.lean"
    files = [root] if root.is_file() else []
    pkg = submission / "LeanUnitary"
    if pkg.is_dir():
        files += sorted(p for p in pkg.rglob("*.lean") if p.is_file())
    return files


def _scan(submission: Path, files: list[Path]) -> list[str]:
    problems = []
    for path in files:
        rel = path.relative_to(submission).as_posix()
        if rel == "LeanUnitary/Spec.lean":
            continue  # replaced by the frozen copy
        code = _strip_comments(path.read_text(errors="replace"))
        for pattern, what in FORBIDDEN:
            if m := re.search(pattern, code):
                line = code.count("\n", 0, m.start()) + 1
                problems.append(f"{rel}:{line}: {what} are not allowed")
    return problems


def _lake() -> str:
    found = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not Path(found).exists():
        raise FileNotFoundError("lake not found; install elan (https://github.com/leanprover/elan)")
    return found


def _run(cmd: list[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=os.environ.copy()
    )


def _tail(text: str) -> str:
    return "\n".join(text.strip().splitlines()[-LOG_TAIL_LINES:])


def _deps_dir() -> Path:
    """Prebuilt dependencies (Mathlib, Quantumlib, ...) for the frozen pins, built once per machine."""
    pins = hashlib.sha256(
        b"".join((FROZEN / f).read_bytes() for f in BUILD_FILES)
    ).hexdigest()[:16]
    deps = Path(os.environ.get("LEAN_UNITARY_HILL_CACHE", Path.home() / ".cache" / "lean-unitary-hill"))
    deps = deps / f"deps-{pins}"
    ready = deps / ".ready"
    if ready.exists():
        return deps
    deps.mkdir(parents=True, exist_ok=True)
    with open(deps / ".lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)  # one bootstrap at a time
        if ready.exists():
            return deps
        for f in BUILD_FILES:
            shutil.copy2(FROZEN / f, deps / f)
        (deps / "LeanUnitary.lean").write_text("")
        lake = _lake()
        for cmd in ([lake, "exe", "cache", "get"], [lake, "build", "Quantumlib"]):
            proc = _run(cmd, deps, BUILD_TIMEOUT_S)
            if proc.returncode != 0:
                raise RuntimeError(f"dependency bootstrap `{' '.join(cmd[1:])}` failed:\n"
                                   + _tail(proc.stdout + proc.stderr))
        ready.touch()
    return deps


def _score(result: dict, final: bool) -> dict:
    claim = result["result"]
    if claim["status"] != "proved":
        return _fail(f"no accepted synthesis theorem: {claim.get('message', claim['status'])}",
                     bounds=claim.get("bounds"))
    per_n, ratios = {}, []
    for n in QUBITS:
        bound, lb = claim["bounds"][str(n)], LOWER_BOUND[n]
        if bound < lb:
            return _fail(
                f"proved bound {bound} for n={n} is below the lower bound {lb}; "
                "the frozen spec must be wrong. Stop and report this to the hill author."
            )
        ratios.append(bound / lb)
        per_n[str(n)] = {"bound": bound, "lower_bound": lb, "ratio": round(bound / lb, 6)}
    return {
        "passed": True,
        "metrics": [{"name": "cnot_ratio", "value": round(sum(ratios) / len(ratios), 6),
                     "direction": "min"}],
        "config": [
            {"name": "mode", "value": "test" if final else "validation", "primary": True},
            {"name": "qubits", "value": f"{QUBITS.start}..{QUBITS.stop - 1}", "primary": True},
            {"name": "lean_toolchain", "value": (FROZEN / "lean-toolchain").read_text().strip(),
             "primary": False},
        ],
        "details": {"per_n": per_n, "declarations_rechecked": result.get("replayed")},
    }


def eval(submission: Path, *, final: bool = False) -> dict:
    submission = Path(submission)
    files = _submission_sources(submission)
    if not (submission / "LeanUnitary.lean").is_file():
        return _fail("submission must contain LeanUnitary.lean (the library root)")
    if not (submission / "LeanUnitary" / "Claims.lean").is_file():
        return _fail("submission must contain LeanUnitary/Claims.lean")
    if problems := _scan(submission, files):
        return _fail("forbidden constructs in submission", problems=problems)

    try:
        deps = _deps_dir()
        lake = _lake()
    except (RuntimeError, FileNotFoundError, subprocess.TimeoutExpired) as e:
        return _fail(f"evaluator setup failed: {e}")

    with tempfile.TemporaryDirectory(prefix="lean-unitary-eval-") as tmp:
        work = Path(tmp)
        for f in BUILD_FILES:
            shutil.copy2(FROZEN / f, work / f)
        for path in files:
            dest = work / path.relative_to(submission)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, dest)
        shutil.copy2(FROZEN / "Spec.lean", work / "LeanUnitary" / "Spec.lean")
        shutil.copy2(FROZEN / "Checker.lean", work / "Checker.lean")
        (work / ".lake").mkdir()
        (work / ".lake" / "packages").symlink_to(deps / ".lake" / "packages")

        try:
            build = _run([lake, "build", "LeanUnitary", "LeanUnitary.Claims"], work, BUILD_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            return _fail(f"lake build exceeded {BUILD_TIMEOUT_S}s")
        if build.returncode != 0:
            return _fail("lake build failed", log=_tail(build.stdout + build.stderr))

        cmd = [lake, "env", "lean", "--run", "Checker.lean", *CHECKER_ARGS]
        try:
            check = _run(cmd, work, CHECK_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            return _fail(f"claim checker exceeded {CHECK_TIMEOUT_S}s")
        try:
            result = json.loads(check.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            return _fail("claim checker crashed", log=_tail(check.stdout + check.stderr))

    if not result.get("ok"):
        return _fail(result.get("error", "claim checker rejected the submission"))
    return _score(result, final)
