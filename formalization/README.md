# Finite Gaussian minimum purification

This is a pinned Lean4 project formalizing the finite-mode Gaussian minimum-purification theorem for both bosons and fermions. The primary roots are:

- `Gaussian.Physical.Boson.exists_matched_global_gaussian_purification`
- `Gaussian.Physical.Fermion.exists_matched_global_gaussian_purification`

Each returns an actual pure Gaussian density with auxiliary sizes exactly matching the two physical parties, attains the infimum, and compares its actual AA′ entropy with every independently finite auxiliary pair. The bosonic density is a positive trace-class operator on full Schrödinger L² space; the fermionic density acts on the full finite occupation space and uses signed complete-mode CAR restrictions. The project does not assert uniqueness, an explicit value formula, non-Gaussian optimality, an infinite-mode theorem, or the optional fixed-total-parity value corollary.

## Exact environment

- Lean4.34.1, selected by `lean-toolchain`
- Lake5.0.0-src+5045d00, distributed with that Lean release
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Physlib `af484f78ee0701290595f8bf892b157b10d64940`
- All transitive package commits are fixed in `lake-manifest.json`

Install the official Lean toolchain with elan, plus Git and Python3. From this directory run:

```sh
lake env lean --version
python3 build_serial.py
```

The script lets Lake resolve the committed lock, verifies every dependency HEAD, builds the project and selected Physlib modules in dependency order, runs ordinary `lake build`, checks both root axiom sets, and records exact commands, exits, versions and source hashes in `build-evidence/`. It does not use any campaign-specific path or wrapper. The serial module order reduces peak memory; the project uses `-j1` for each Lean invocation.

A normal direct build is also:

```sh
lake build
```

The initial dependency download requires network access to the exact repositories in the lock. Official mathlib/dependency release caches can accelerate the build; they are optional for correctness. No Gaussian or implementer-compiled Physlib cache is required. Unrelated upstream Physlib files may contain unfinished work; this project imports only the source closure actually rebuilt and audited. Do not replace its selected imports with an import of the whole upstream library.

The mathematical definitions and proofs contain no `sorry`, `admit`, project axiom, or unsafe proof premise. Root axiom audits admit only `propext`, `Classical.choice`, and `Quot.sound`. The final verification status and exact audit/rebuild provenance belong to the accompanying reports; building the project alone does not establish that the required independent audits have completed.

The source identity being formalized is LeoLam233/gaussian-minimum-purification tag v0.1.2, commit `f0d0ba959472bf4eda97319b8d79fe51461e0b60`, tree `91b29c15888b58caf088477fd8577f78a3e3a144`. No remote repository was modified.
