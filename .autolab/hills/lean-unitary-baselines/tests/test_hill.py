"""Checks on the hill itself, run by `hills check`.

The skeleton (every milestone stated, none proved) scores 0, and each way of faking a
milestone is rejected. Tests that build Lean take a minute or two each.
"""

import shutil
import sys
from pathlib import Path

import pytest
from hills import run_evaluator

HILL = Path(__file__).resolve().parents[1]
SKELETON = HILL / "examples" / "skeleton"

sys.path.insert(0, str(HILL))
import eval as hill_eval  # noqa: E402

HEADER = "import LeanUnitary.Spec\nopen LeanUnitary.Spec\nnamespace LeanUnitary.Claims\n"


def _submission(tmp_path: Path, claims_body: str) -> Path:
    sub = tmp_path / "sub"
    shutil.copytree(SKELETON, sub)
    (sub / "LeanUnitary" / "Claims.lean").write_text(
        HEADER + claims_body + "\nend LeanUnitary.Claims\n"
    )
    return sub


def test_skeleton_scores_zero():
    result = run_evaluator(HILL, SKELETON)
    assert result["passed"], result["details"]
    assert result["metrics"] == [{"name": "milestone_points", "value": 0, "direction": "max"}]
    primary = {c["name"]: c["value"] for c in result["config"] if c["primary"]}
    assert primary == {"mode": "validation", "max_points": 19}
    milestones = result["details"]["milestones"]
    assert set(milestones) == set(hill_eval.MILESTONES)
    for entry in milestones.values():
        assert entry["status"] == "rejected"
        assert "sorryAx" in entry["message"]  # statements match; only the proofs are missing


def test_missing_claims_is_rejected(tmp_path):
    sub = tmp_path / "sub"
    shutil.copytree(SKELETON, sub)
    (sub / "LeanUnitary" / "Claims.lean").unlink()
    result = run_evaluator(HILL, sub)
    assert not result["passed"]
    assert "Claims.lean" in result["details"]["error"]


@pytest.mark.parametrize(
    "body",
    [
        "axiom magic : QSD\ntheorem qsd : QSD := magic",
        "theorem twoQubitOptimal : TwoQubitOptimal := by native_decide",
        "#eval IO.println \"hi\"",
        "-- axiom in a comment is fine\n/- so is #eval -/\nset_option debug.skipKernelTC true",
    ],
)
def test_forbidden_constructs_are_rejected_before_building(tmp_path, body):
    result = run_evaluator(HILL, _submission(tmp_path, body))
    assert not result["passed"]
    assert result["details"]["error"] == "forbidden constructs in submission"
    assert len(result["details"]["problems"]) == 1


def test_fake_milestones_do_not_score(tmp_path):
    body = "\n".join([
        "theorem qsd : Synthesizable 2 6 := sorry",          # wrong statement
        "def blockZXZ : BlockZXZ := sorry",                  # not a theorem
        "theorem twoQubitOptimal : Synthesizable 2 3 := sorry",  # unfolds to it, but sorry
    ])
    result = run_evaluator(HILL, _submission(tmp_path, body))
    assert result["passed"], result["details"]
    assert result["metrics"][0]["value"] == 0
    m = result["details"]["milestones"]
    assert "must be `LeanUnitary.Spec.QSD`" in m["QSD"]["message"]
    assert "must be a theorem" in m["BlockZXZ"]["message"]
    assert "sorryAx" in m["TwoQubitOptimal"]["message"]
    assert m["MuxRotations"]["status"] == "missing"


def test_points_arithmetic():
    result = {"replayed": 1, "result": [
        {"milestone": "MuxRotations", "status": "proved"},
        {"milestone": "CosineSine", "status": "proved"},
        {"milestone": "QSD", "status": "rejected", "message": "x"},
    ]}
    report = hill_eval._score(result, final=False)
    assert report["metrics"][0]["value"] == 2 + 3
    assert report["details"]["milestones"]["Demultiplex"]["status"] == "missing"
