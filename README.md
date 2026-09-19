# Small-order biplanar coloring

A computer-assisted proof that every finite simple biplanar graph on at most 18 vertices is 9-colorable, developed while searching for a 10-chromatic example for the Earth–Moon problem. The Lean development is a compiled **partial formalization**: graph-reduction and finite-case hypotheses remain unproved, and planarity is an abstract parameter.

## Dependencies

Lean **4.34.0** through Elan/Lake (no mathlib), **Python 3.13**, the packages in `requirements.txt`, and the **Z3 shared library**. On Debian/Ubuntu, install Z3 with `sudo apt install libz3-4`; set `Z3_LIBRARY` to its library path if automatic discovery fails.

## Run

With Elan and Z3 installed, run from the repository root:

```sh
elan toolchain install "$(cat lean-toolchain)"
python3.13 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
sha256sum -c MANIFEST.sha256
python -m unittest -v test_check_lean
python check_project.py --require-lean
```

This runs the computational checks, Lean build, and axiom audit. GitHub Actions runs the same suite. For Lean alone, use `python check_lean.py`.

## Files

```text
earth_moon_small_order_proof.md  Mathematical proof through order 18
SmallOrder.lean                 Partial Lean formalization
arithmetic_check.py            Arithmetic and table checks
check_project.py               Full verification runner
check_lean.py                  Lean build and axiom audit
computations/                  Graph data and computational verifiers
verification/                  Recorded Lean build evidence
.github/workflows/lean.yml      Full verification workflow
```

Fresh reports are written to `verification.json`, `lean_verification.json`, and `computations/`.
