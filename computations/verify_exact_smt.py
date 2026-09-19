#!/usr/bin/env python3
"""Recheck the 90 reconstructed integer models with exact SMT arithmetic.

Reuses the independently reconstructed constraints from verify_sat_independent,
not the original SMT-LIB dumps. Converts each integral row to a pseudo-Boolean
inequality in the Z3 C API. No floating-point feasibility tolerance is involved.
This is still an external solver check, not a Lean/LRAT proof certificate.

Requires the same Python packages as the MILP verifier and a shared libz3.
Set Z3_LIBRARY to its absolute path when automatic discovery is unavailable.
"""
from __future__ import annotations

import ctypes as C
import ctypes.util
import json
import math
import os
from pathlib import Path
import time

import verify_sat_independent as models

ROOT = Path(__file__).resolve().parent
PTR = C.c_void_p
UINT = C.c_uint
INT = C.c_int
TEXT = C.c_char_p
PTR_ARRAY = C.POINTER(PTR)
INT_ARRAY = C.POINTER(INT)


def load_z3() -> C.CDLL:
    name = os.environ.get("Z3_LIBRARY") or ctypes.util.find_library("z3")
    if not name:
        raise RuntimeError("Shared libz3 not found; set Z3_LIBRARY to its absolute path")
    library = C.CDLL(name)
    signatures = {
        "mk_config": (PTR, []),
        "del_config": (None, [PTR]),
        "set_param_value": (None, [PTR, TEXT, TEXT]),
        "mk_context": (PTR, [PTR]),
        "del_context": (None, [PTR]),
        "mk_string_symbol": (PTR, [PTR, TEXT]),
        "mk_bool_sort": (PTR, [PTR]),
        "mk_const": (PTR, [PTR, PTR, PTR]),
        "mk_solver": (PTR, [PTR]),
        "solver_inc_ref": (None, [PTR, PTR]),
        "solver_dec_ref": (None, [PTR, PTR]),
        "solver_assert": (None, [PTR, PTR, PTR]),
        "solver_check": (INT, [PTR, PTR]),
        "solver_get_reason_unknown": (TEXT, [PTR, PTR]),
        "mk_pble": (PTR, [PTR, UINT, PTR_ARRAY, INT_ARRAY, INT]),
        "mk_pbge": (PTR, [PTR, UINT, PTR_ARRAY, INT_ARRAY, INT]),
        "get_full_version": (TEXT, []),
    }
    for name, (out, args) in signatures.items():
        fun = getattr(library, "Z3_" + name)
        fun.restype, fun.argtypes = out, args
    return library


Z3 = load_z3()


def integral(value: float) -> int:
    result = int(value)
    if result != value or not -(2**31) < result < 2**31:
        raise ValueError(f"Nonintegral or oversized pseudo-Boolean coefficient: {value}")
    return result


def exact_solve(model: models.Model) -> dict:
    cfg = Z3.Z3_mk_config()
    Z3.Z3_set_param_value(cfg, b"timeout", b"90000")
    ctx = Z3.Z3_mk_context(cfg)
    Z3.Z3_del_config(cfg)
    solver = Z3.Z3_mk_solver(ctx)
    Z3.Z3_solver_inc_ref(ctx, solver)
    try:
        sort = Z3.Z3_mk_bool_sort(ctx)
        variables = [Z3.Z3_mk_const(ctx, Z3.Z3_mk_string_symbol(ctx, f"x{i}".encode()), sort)
                     for i in range(model.n)]
        for row, lower, upper in zip(model.rows, model.lb, model.ub):
            terms = [(i, integral(c)) for i, c in row.items() if c]
            asts = (PTR * len(terms))(*(variables[i] for i, _ in terms))
            coefficients = (INT * len(terms))(*(c for _, c in terms))
            if math.isfinite(lower):
                Z3.Z3_solver_assert(ctx, solver,
                    Z3.Z3_mk_pbge(ctx, len(terms), asts, coefficients, integral(lower)))
            if math.isfinite(upper):
                Z3.Z3_solver_assert(ctx, solver,
                    Z3.Z3_mk_pble(ctx, len(terms), asts, coefficients, integral(upper)))
        result = Z3.Z3_solver_check(ctx, solver)
        status = {-1: "unsat", 0: "unknown", 1: "sat"}[result]
        record = {"status": status, "variables": model.n, "constraints": len(model.rows)}
        if result == 0:
            record["reason"] = Z3.Z3_solver_get_reason_unknown(ctx, solver).decode()
        return record
    finally:
        Z3.Z3_solver_dec_ref(ctx, solver)
        Z3.Z3_del_context(ctx)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; the input reconstruction validates cuts with assertions")
    # Substitute the solve backend only. Both family builders remain unchanged.
    models.Model.solve = exact_solve
    started = time.perf_counter()
    records = []
    families = [("critical13_K6_results", models.critical13),
                ("attachment_results", models.attachment)]
    for family, build in families:
        data = json.loads((ROOT / f"{family}.json").read_text())
        if not data["complete"]:
            raise RuntimeError(f"Incomplete input family: {family}")
        for base in data["results"]:
            t = time.perf_counter()
            result = build(base)
            result.update(family=family, base_index=base["base_index"], seconds=time.perf_counter() - t)
            records.append(result)
            print(f"{family} {base['base_index']}: {result['status']}", flush=True)
            if result["status"] != "unsat":
                raise RuntimeError(result)
    if len(records) != 90:
        raise RuntimeError(f"Expected 90 exclusions, obtained {len(records)}")
    out = {"status": "passed", "solver": "Z3", "version": Z3.Z3_get_full_version().decode(),
           "arithmetic": "integral pseudo-Boolean", "all_unsat": True,
           "seconds": time.perf_counter() - started, "results": records}
    (ROOT / "exact_smt_verification.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"PASS: 90 exact-arithmetic SMT exclusions in {out['seconds']:.3f}s")


if __name__ == "__main__":
    main()
