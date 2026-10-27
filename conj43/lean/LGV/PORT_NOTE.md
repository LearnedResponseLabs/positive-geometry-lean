# Vendored port of LeanLGV

Source: https://github.com/PerAlexandersson/LeanLGV, commit acf9f6694c1169e9773aaf9d1d594709c0926eb8 (Apache-2.0, `LICENSE` in this directory).
Copyright (c) 2026 Per Alexandersson; the original notices are kept in every file.

Modifications (2026-10-08): `Quiver/Path.lean` imports `Mathlib.Data.Finite.Prod` and `Mathlib.Data.Finite.Sigma`
instead of `Mathlib.Basic.Finite.Prod` and `Mathlib.Basic.Finite.Sigma` (module names at this project's Mathlib pin),
with a notice in that file. No other file is changed.
