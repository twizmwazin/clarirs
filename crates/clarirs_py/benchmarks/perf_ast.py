from __future__ import annotations

import clarirs
from clarirs.ast.base import Base


class MyAnnotation(clarirs.Annotation):
    def __init__(self, value):
        self.value = value

    def __repr__(self):
        return f"MyAnnotation({self.value})"


def make_asts() -> list[Base]:
    results: list[Base] = []

    # Make a lot of BVS
    results.extend([clarirs.BVS(str(i), 32) for i in range(1000)])

    # Make a lot of BVV
    results.extend([clarirs.BVV(i, 32) for i in range(1000)])

    # Make a lot of And
    results.extend([clarirs.And(clarirs.BVS(str(i), 32), clarirs.BVV(i, 32)) for i in range(1000)])

    # Make a lot of Or
    results.extend([clarirs.Or(clarirs.BVS(str(i), 32), clarirs.BVV(i, 32)) for i in range(1000)])

    # Make a lot of FPS
    results.extend([clarirs.FPS(str(i), clarirs.FSORT_DOUBLE) for i in range(1000)])

    # Make a lot of FPV
    results.extend([clarirs.FPV(i, clarirs.FSORT_DOUBLE) for i in range(1000)])

    # Annotate!
    # for i in range(100):
    #     for j in range(10):
    #         results[i] = results[i].append_annotation(MyAnnotation(j))

    return results

def test_perf_ast():
    for i in range(1000):
        make_asts()

test_perf_ast()
