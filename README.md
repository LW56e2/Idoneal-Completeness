# Euler's list of idoneal numbers is complete (Lean 4)

In the form used here, a positive integer `n` is *idoneal* when it is **not** of the form
`ab + bc + ca` with `0 < a < b < c`. Euler's list has 65 such numbers, the largest being 1848.
This repository contains a Lean 4 proof that there are no others:

```lean
theorem idoneal_numbers_completeness :
    ∀ n : ℕ, Idoneal.IsIdoneal n → n ∈ Idoneal.knownIdonealNumbers

theorem isIdoneal_iff_mem_knownIdonealNumbers (n : ℕ) :
    Idoneal.IsIdoneal n ↔ n ∈ Idoneal.knownIdonealNumbers
```

Both theorems are in [`IdonealUnconditional.lean`](IdonealUnconditional.lean) and depend on the
axioms `propext`, `Classical.choice` and `Quot.sound` only. The definitions `IsIdoneal` and
`knownIdonealNumbers` ([`Idoneal/Defs.lean`](Idoneal/Defs.lean)) are copied word for word from
`FormalConjectures/Wikipedia/IdonealCompleteness.lean` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
where the first statement is tagged `research open`.

## What the proof rests on

1. **A zero-free half-plane** (`vendor/quasi-riemann-improved`). The theorem
   `RH.Transport.dirichlet_nonvanishing` says that no Dirichlet L-function vanishes at a point with
   `Re s > 4374785349/5000000000`, apart from the pole of the trivial character at `s = 1`. It is
   proved in the project `quasi-riemann-improved`; an unchanged copy of its commit
   `b83dbbd914c5751acf9bc3389cde58970437278f` is kept in `vendor/` (git tree
   `c9e1e71711003e96369043cee9a867e8ae36f2c9`, so
   `git rev-parse HEAD:vendor/quasi-riemann-improved` prints that hash here too).
2. **This repository's own part** (`Idoneal/`). If no Dirichlet L-function of a nontrivial
   character has a real zero in `[19/20, 1)`, then the list is complete
   (`Idoneal.idoneal_numbers_completeness_of_noRealZeros` in
   [`Idoneal/Main.lean`](Idoneal/Main.lean); the same from any zero-free half-plane `Re s > T` with
   `T < 19/20`). The converse, that the 65 listed numbers are idoneal, needs no hypothesis
   (`Idoneal.isIdoneal_of_mem_known`).

The route of part 2 is elementary (no class number formula): a number without a triple has only
"ambiguous" reduced forms, at most `τ(n)` of them; counting roots of `b² ≡ -n` against lattice
points in ellipses gives `2·L(1, χ) ≤ π·τ(n)/√n`; a Pintz-type argument gives
`L(1, χ) ≥ 1/(2(log n + 16))` when `L(β, χ) ≥ 0` near 1. So `√n ≤ π·τ(n)·(log n + 16)` for
squarefree `n ≥ 10⁶` without a triple, which leaves six finite classes and all `n < 4·10⁶`; these
are settled by kernel computation (`decide +kernel`, never `native_decide`). The full plan is in
[`BLUEPRINT.md`](BLUEPRINT.md).

## Layout

| path | content |
|---|---|
| `Idoneal/` | the conditional theorem: definitions, theory, checkers (`ComputeCore.lean`), the 14 kernel-run files (`ComputeRuns/`), `Main.lean` |
| `IdonealUnconditional.lean` | the two theorems above, one line each |
| `vendor/quasi-riemann-improved/` | the zero-free project (package `RHTransport`, libraries `OAI` and `Transport`), unchanged |
| `scripts/` | `apply-patches.sh` and two files that print statements and axioms |
| `logs/2026-11-16/` | build, axiom and re-check logs of the verification run |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | one Lake workspace; every dependency is pinned |

## Build

Prerequisites: Git and [elan](https://github.com/leanprover/elan). The toolchain file pins
Lean 4.34.1 and the lockfile pins every dependency, including Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Do not run `lake update`.

```sh
lake env lean --version      # Lake fetches the packages pinned in lake-manifest.json
scripts/apply-patches.sh     # two compatibility patches required by the vendored project
lake exe cache get           # Mathlib's prebuilt cache
lake build Idoneal           # the conditional theorem (needs Mathlib only)
lake build                   # everything, including the vendored project
```

The patches are the ones described in `vendor/quasi-riemann-improved/README.md`; they adapt
`rellich-kondrachov` and `PrimeNumberTheoremAnd` to Lean 4.34.1 and their hashes are recorded in
`vendor/quasi-riemann-improved/lean/upstream-config/applied-physical-patches.json`. Lake then warns
that these two packages have local changes; that is expected.

Cost, as measured on 16 Nov 2026 on an AMD EPYC 9684X:

* `lake build Idoneal`: the theory files take a minute or two; the 14 run files prove 117 facts by
  kernel computation and took 7.6 minutes with all 14 in parallel (about 76 CPU-minutes; each
  process reaches about 10 GB resident memory, some 4 GB of it private).
* `lake build`: 77.5 minutes. The final theorem needs 3 055 of the 3 059 files of the vendored
  project and their import chain is 409 files deep, so the time is set by single-core speed, not by
  the number of cores.
* With very many cores, raise the open-file limit before `lake exe cache get`
  (`ulimit -n 65536`) and cap Lake's parallelism if memory is short (`LEAN_NUM_THREADS=44`).

## Check the statements and the axioms

```sh
lake env lean scripts/AxiomsConditional.lean
lake env lean scripts/AxiomsUnconditional.lean
```

Every line of the form `'…' depends on axioms:` must list `propext`, `Classical.choice`,
`Quot.sound` and nothing else.

## Verification record

All of the following is in `logs/2026-11-16/`.

* **Build** on a rented Linux box (AMD EPYC 9684X): the conditional project (`full.log`, 8 953
  jobs) and the workspace joining it with `quasi-riemann-improved` (`uncond.log`, 12 031 jobs,
  4 652 s), both without error and without a `sorry` warning. `uncond.first-try.log` is an earlier
  attempt that failed because the two patches had not been applied yet.
* **Axioms** printed there: `axfinal.out` (conditional theorems) and `axuncond.out`
  (unconditional theorems and `RH.Transport.dirichlet_nonvanishing`): the three standard axioms
  only.
* **Independent re-check** with the toolchain's `leanchecker`, which replays the declarations of
  a module through the kernel again (`recheck/`): each of the 28 modules of `Idoneal/` that
  contain declarations, kernel computations included, and `IdonealUnconditional`; all 29 exit
  with code 0. Not re-checked this way: the root module `Idoneal` (it has no declarations; given
  that name the tool replays everything below it at once and ran out of memory,
  `recheck/Idoneal.out`), the vendored project and the libraries.
* **Second machine**: the build outputs were copied to a Mac (compared by checksum); there
  `lake build --no-build` reports every target up to date (`mac-uncond-nobuild.log`) and the
  axioms print the same (`mac-axuncond.out`).

During that run the two projects lay side by side and the joining file had a small package of its
own; this repository holds the same Lean files in one workspace.

## Provenance and licences

* `vendor/quasi-riemann-improved` is under the Apache License 2.0 (`LICENSE` in that folder). Its
  `lean/OAI` sources come from `openai/math`; their manifest, licence and the two patches are in
  `lean/upstream-config`.
* `Idoneal/Defs.lean` copies two definitions from `google-deepmind/formal-conjectures`
  (Apache License 2.0, Copyright 2026 The Formal Conjectures Authors).
