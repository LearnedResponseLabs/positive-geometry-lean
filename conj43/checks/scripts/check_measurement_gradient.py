#!/usr/bin/env python3
"""Finite convention check, not a proof; no exponent-matrix construction/import.

Galashin arXiv:2102.13339v2 Def. 1.15 supplies actual curve evaluations.
The left twist is solved from its duality equations on reverse necklaces.
The independent RHS uses the resolved oriented crossing predicate and affine angles.
Two deterministic distinct-parameter configurations per non-top cell, 2 <= n <= 7.
Requires NumPy; run with OPENBLAS_NUM_THREADS=1 for a predictable small footprint.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

import numpy as np

OUT = Path(__file__).resolve().parents[1] / "out" / "measurement_gradient.json"
TOL = 1e-8


def cell_data(sigma):
    n = len(sigma)
    inv = np.argsort(sigma)
    rows = [{x for x in range(n) if inv[x] >= x}]
    for r in range(n - 1):
        assert r in rows[-1]
        rows.append((rows[-1] - {r}) | {sigma[r]})
    edges = []
    for p, q in itertools.permutations(range(n), 2):
        endpoints = [5 * inv[p] + 4, 5 * inv[q] + 4, 5 * p + 1, 5 * q + 1]
        steps = [(endpoints[(i + 1) % 4] - endpoints[i]) % (5 * n) for i in range(4)]
        if min(steps) > 0 and sum(steps) == 5 * n:
            edges.append((p, q))
    lift = [s if s > i else s + n for i, s in enumerate(sigma)]
    return inv, rows, edges, lift


def configs(n, edges, seed):
    # First point is cyclically ordered, asymmetric and away from walls.
    rng = np.random.default_rng(seed)
    gaps = rng.uniform(0.75, 1.25, n)
    theta = np.r_[0.0, np.cumsum(gaps[:-1])] * math.pi / gaps.sum()
    yield theta.copy()
    # Move inside the full crossing chamber, allowing noncrossing labels to reorder.
    for _ in range(80):
        proposal = theta.copy()
        proposal[rng.integers(n)] += rng.uniform(-0.65, 0.65)
        delta = [proposal[q] - proposal[p] + math.pi * (p > q) for p, q in edges]
        if delta and not (min(delta) > 0.12 and max(delta) < math.pi - 0.12):
            continue
        separation = [abs(math.sin(proposal[p] - proposal[q]))
                      for p, q in itertools.combinations(range(n), 2)]
        if min(separation) > 0.025:
            theta = proposal
    yield theta.copy()


def observable(sigma, theta, inv, rows, lift):
    n, k = len(sigma), len(rows[0])
    # Evaluation basis for degree k-1 trigonometric polynomials, not necklace exponents.
    t = (np.arange(k) + 0.413) * math.pi / k
    A = np.empty((k, n))
    for r in range(n):
        roots = sorted(rows[r] - {r})
        epsilon = (-1) ** sum(sigma[p] <= p < r for p in range(n))
        A[:, r] = epsilon * np.prod(np.sin(t[:, None] - theta[roots]), axis=1)
    singular = np.linalg.svd(A, compute_uv=False)
    if singular[-1] <= 1e-12 * singular[0]:
        raise ArithmeticError("curve basis numerically rank deficient")
    # An invertible row-basis change: improve conditioning without changing the plane.
    A = np.linalg.qr(A.T, mode="reduced")[0].T
    twist = np.empty_like(A)
    max_condition = 0.0
    for r in range(n):
        js = [j for j in range(r - n, r + 1)
              if j <= r < lift[j % n] + (j // n) * n]
        assert len(js) == k and r in js
        system = np.array([(-1.0) ** ((k - 1) * (j // n)) * A[:, j % n] for j in js])
        max_condition = max(max_condition, float(np.linalg.cond(system)))
        twist[:, r] = np.linalg.solve(system, np.array([float(j == r) for j in js]))
    log_minor = []
    for row in rows:
        sign, logdet = np.linalg.slogdet(twist[:, sorted(row)])
        if sign == 0 or not np.isfinite(logdet):
            raise ArithmeticError("zero/nonfinite twisted necklace minor")
        log_minor.append(logdet)
    differences = np.roll(log_minor, -1) - log_minor
    return differences[inv], max_condition


def main():
    start = time.monotonic()
    records, failures = [], []
    for n in range(2, 8):
        for index, sigma in enumerate(itertools.permutations(range(n))):
            if any(all(sigma[i] == (i + k) % n for i in range(n)) for k in range(1, n + 1)):
                continue  # Galashin's top cells, already covered by the earlier control.
            inv, rows, edges, lift = cell_data(sigma)
            B = np.zeros((n, len(edges)))
            for j, (p, q) in enumerate(edges):
                B[p, j], B[q, j] = -1, 1
            for sample, theta in enumerate(configs(n, edges, 100003 * n + index)):
                entry = {"n": n, "sigma_1based": [x + 1 for x in sigma], "sample": sample,
                         "rank": len(rows[0]), "edges": len(edges),
                         "coloops": sum(i == s for i, s in enumerate(sigma)),
                         "wrapped_edges": sum(p > q for p, q in edges),
                         "nonmonotone_angles": bool(np.any(np.diff(theta) < 0)),
                         "theta": theta.tolist()}
                try:
                    lhs, condition = observable(sigma, theta, inv, rows, lift)
                    delta = np.array([theta[q] - theta[p] + math.pi * (p > q) for p, q in edges])
                    assert all(0 < d < math.pi for d in delta)
                    ell = np.log(np.sin(delta))
                    rhs = B @ ell
                    error = float(np.max(np.abs(lhs - rhs)))
                    entry.update(error=error, max_twist_condition=condition,
                                 obtuse_edges=int(np.sum(delta > math.pi / 2)))
                    if error >= TOL:
                        raise ArithmeticError(f"identity residual {error}")
                    # Per-edge reversal preserves sin(delta), but reverses its B column.
                    if edges:
                        wrapped = [j for j, (p, q) in enumerate(edges) if p > q]
                        assert wrapped
                        j = max(wrapped, key=lambda j: abs(ell[j]))
                        mutant = rhs - 2 * B[:, j] * ell[j]
                        mutation_error = float(np.max(np.abs(lhs - mutant)))
                        entry["reversed_wrapped_edge_1based"] = [x + 1 for x in edges[j]]
                        entry["mixed_orientation_error"] = mutation_error
                        entry["mixed_orientation_rejected"] = mutation_error > TOL
                        entry["missing_wrap_rejected"] = bool(theta[edges[j][1]] - theta[edges[j][0]] < 0)
                        if not entry["mixed_orientation_rejected"] or not entry["missing_wrap_rejected"]:
                            raise ArithmeticError("a planted orientation/lift error was not rejected")
                    else:
                        entry["control_scope"] = "vacuous: no crossing edge to mutate"
                except Exception as exc:
                    entry["failure"] = f"{type(exc).__name__}: {exc}"
                    failures.append(entry)
                records.append(entry)
        print(f"n={n}: {len(records)} points, {len(failures)} failures", flush=True)
    edge_records = [r for r in records if r["edges"]]
    report = {
        "status": "PASS_FINITE_NUMERICAL_INTERFACE" if not failures else "FAIL",
        "scope": "Two distinct-parameter points per non-top loopless cell, 2<=n<=7; not a theorem or a collision check.",
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "numpy_version": np.__version__, "python_version": sys.version,
        "tolerance": TOL, "non_top_cells": len(records) // 2, "points": len(records),
        "nonvacuous_points": len(edge_records), "vacuous_points": len(records) - len(edge_records),
        "points_with_coloops": sum(r["coloops"] > 0 for r in records),
        "nonmonotone_points": sum(r["nonmonotone_angles"] for r in records),
        "points_with_obtuse_edges": sum(r.get("obtuse_edges", 0) > 0 for r in records),
        "max_error": max((r.get("error", 0) for r in records), default=0),
        "max_twist_condition": max((r.get("max_twist_condition", 0) for r in records), default=0),
        "mixed_orientation_rejected": sum(r.get("mixed_orientation_rejected", False) for r in records),
        "missing_wrap_rejected": sum(r.get("missing_wrap_rejected", False) for r in records),
        "failures": failures, "wall_seconds": time.monotonic() - start,
        "records": records,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"records", "failures"}}, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
