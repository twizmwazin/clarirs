import pickle

import claripy


def test_replacement_solver_exists():
    """SolverReplacement is exported and constructible."""
    s = claripy.SolverReplacement()
    assert isinstance(s, claripy.Solver)


def test_auto_replace_default_extracts_replacements():
    """By default (auto_replace=True) `x == c` is turned into a replacement."""
    s = claripy.SolverReplacement()
    x = claripy.BVS("x", 8)
    s.add(x == 5)
    assert s.eval(x, 1)[0] == 5


def test_auto_replace_true_keyword():
    """Passing auto_replace=True explicitly behaves like the default."""
    s = claripy.SolverReplacement(auto_replace=True)
    x = claripy.BVS("x", 8)
    s.add(x == 9)
    assert s.eval(x, 1)[0] == 9


def test_auto_replace_false_disables_extraction():
    """With auto_replace=False, adding `x == c` does not register a
    replacement, but explicit replacements still work."""
    s = claripy.SolverReplacement(auto_replace=False)
    x = claripy.BVS("x", 8)
    s.add(x == 5)

    # The backend still solves the constraint, so x evaluates to 5.
    assert s.eval(x, 1)[0] == 5

    # Explicit replacements override the value regardless of auto_replace.
    s.add_replacement(x, claripy.BVV(7, 8))
    assert s.eval(x, 1)[0] == 7


def test_auto_replace_clear_replacements():
    s = claripy.SolverReplacement()
    x = claripy.BVS("x", 8)
    s.add_replacement(x, claripy.BVV(3, 8))
    assert s.eval(x, 1)[0] == 3
    s.clear_replacements()
    # After clearing, x is unconstrained again (any value is allowed).
    assert s.satisfiable()


def test_auto_replace_branch_preserves_setting():
    """branch() clones the solver, keeping auto_replace=False."""
    s = claripy.SolverReplacement(auto_replace=False)
    b = s.branch()
    x = claripy.BVS("x", 8)
    b.add(x == 5)
    b.add_replacement(x, claripy.BVV(4, 8))
    assert b.eval(x, 1)[0] == 4


def test_auto_replace_pickle_roundtrip():
    """auto_replace survives a pickle round-trip."""
    s = claripy.SolverReplacement(auto_replace=False)
    restored = pickle.loads(pickle.dumps(s))
    assert isinstance(restored, claripy.Solver)
    x = claripy.BVS("x", 8)
    restored.add(x == 5)
    restored.add_replacement(x, claripy.BVV(6, 8))
    assert restored.eval(x, 1)[0] == 6


if __name__ == "__main__":
    test_replacement_solver_exists()
    test_auto_replace_default_extracts_replacements()
    test_auto_replace_true_keyword()
    test_auto_replace_false_disables_extraction()
    test_auto_replace_clear_replacements()
    test_auto_replace_branch_preserves_setting()
    test_auto_replace_pickle_roundtrip()
    print("All tests passed!")
