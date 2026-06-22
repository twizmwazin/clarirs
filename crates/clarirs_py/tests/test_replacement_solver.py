import claripy


def test_replacement_solver_auto_replace_kwarg():
    # angr constructs SolverReplacement(auto_replace=False); the kwarg (and the
    # standard timeout/track options) must be accepted.
    claripy.SolverReplacement()
    claripy.SolverReplacement(auto_replace=False)
    claripy.SolverReplacement(auto_replace=False, track=True)


def test_replacement_solver_solves():
    s = claripy.SolverReplacement(auto_replace=False)
    x = claripy.BVS("x", 8)
    s.add(x == 5)
    assert s.satisfiable()
    assert s.eval(x, 1)[0] == 5


def test_replacement_solver_auto_replace():
    s = claripy.SolverReplacement()  # auto_replace defaults to True
    x = claripy.BVS("x", 8)
    s.add(x == 5)
    assert s.eval(x + claripy.BVV(1, 8), 1)[0] == 6
