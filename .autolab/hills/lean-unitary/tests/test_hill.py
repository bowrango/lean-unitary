"""Checks on the hill itself, run by `hills check`.

A submission scores only with a complete synthesis theorem. The skeleton states it (with the
block-ZXZ bound) but has not proved it, so it must fail with the bounds reported. Tests that
build Lean take a minute or two each.
"""

import shutil
import sys
from pathlib import Path

import pytest
from hills import run_evaluator

HILL = Path(__file__).resolve().parents[1]
SKELETON = HILL / "examples" / "skeleton"
BASELINE = HILL / "examples" / "baseline"  # a proved algorithm, added once one exists

sys.path.insert(0, str(HILL))
import eval as hill_eval  # noqa: E402

HEADER = "import LeanUnitary.Spec\nopen LeanUnitary.Spec\nnamespace LeanUnitary.Claims\n"
BLOCK_ZXZ = {3: 19, 4: 95, 5: 423, 6: 1783, 7: 7319, 8: 29655}


def _submission(tmp_path: Path, claims_body: str) -> Path:
    sub = tmp_path / "sub"
    shutil.copytree(SKELETON, sub)
    (sub / "LeanUnitary" / "Claims.lean").write_text(
        HEADER + claims_body + "\nend LeanUnitary.Claims\n"
    )
    return sub


def test_unproved_skeleton_is_not_scored():
    result = run_evaluator(HILL, SKELETON)
    assert not result["passed"]
    assert "sorryAx" in result["details"]["error"]
    assert result["details"]["bounds"] == {str(n): k for n, k in BLOCK_ZXZ.items()}


@pytest.mark.skipif(not BASELINE.exists(), reason="no proved baseline algorithm yet")
def test_baseline_scores():
    result = run_evaluator(HILL, BASELINE)
    assert result["passed"], result["details"]
    assert result["metrics"][0]["name"] == "cnot_ratio"
    assert 1 <= result["metrics"][0]["value"] < 2
    primary = {c["name"]: c["value"] for c in result["config"] if c["primary"]}
    assert primary == {"mode": "validation", "qubits": "3..8"}


@pytest.mark.parametrize(
    "body",
    [
        "axiom magic : GeneralBound fun _ => 1\ntheorem synth : GeneralBound fun _ => 1 := magic",
        "theorem synth : GeneralBound fun _ => 1 := by native_decide",
        "#eval IO.println \"hi\"",
    ],
)
def test_forbidden_constructs_are_rejected_before_building(tmp_path, body):
    result = run_evaluator(HILL, _submission(tmp_path, body))
    assert not result["passed"]
    assert result["details"]["error"] == "forbidden constructs in submission"


def test_wrong_statement_is_not_scored(tmp_path):
    result = run_evaluator(HILL, _submission(tmp_path, "theorem synth : BlockZXZ := sorry"))
    assert not result["passed"]
    assert "must be `LeanUnitary.Spec.GeneralBound f`" in result["details"]["error"]


def _checked(bounds: dict) -> dict:
    return {"replayed": 1, "result": {"status": "proved",
                                      "bounds": {str(n): k for n, k in bounds.items()}}}


def test_ratio_arithmetic():
    report = hill_eval._score(_checked(BLOCK_ZXZ), final=False)
    expected = sum(BLOCK_ZXZ[n] / hill_eval.LOWER_BOUND[n] for n in BLOCK_ZXZ) / len(BLOCK_ZXZ)
    assert report["metrics"][0]["value"] == pytest.approx(expected, abs=1e-6)
    assert report["metrics"][0]["value"] == pytest.approx(1.657, abs=1e-3)
    optimal = hill_eval._score(_checked(hill_eval.LOWER_BOUND), final=False)
    assert optimal["metrics"][0]["value"] == 1


def test_bound_below_lower_bound_is_flagged_as_spec_bug():
    bounds = {**BLOCK_ZXZ, 3: 13}
    report = hill_eval._score(_checked(bounds), final=False)
    assert not report["passed"]
    assert "spec must be wrong" in report["details"]["error"]
