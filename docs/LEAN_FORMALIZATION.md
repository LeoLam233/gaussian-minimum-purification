# Lean formalization and reproducibility

Repository release **v0.1.3** adds the already verified, source-only Lean project in [formalization/](../formalization/README.md). The mathematical manuscript and expert brief remain **v0.1.1**. Their theorem and proof are unchanged.

## Formalized result and exact roots

The primary finite-mode Gaussian minimum-purification theorem is formalized for both bosonic and fermionic sectors. The optimization includes **all independently finite auxiliary mode pairs**. Each physical root provides actual matched sidewise auxiliary witnesses attaining the global finite-auxiliary infimum, together with physical state/covariance/entropy semantic bridges.

- `Gaussian.Physical.Boson.exists_matched_global_gaussian_purification`
- `Gaussian.Physical.Fermion.exists_matched_global_gaussian_purification`

The bosonic construction uses positive trace-class densities on full Schrödinger L² space. The fermionic construction uses the full finite occupation space and signed complete-mode CAR restrictions. Statements are under the hypotheses encoded by the named declarations and their definitions; the source is authoritative.

This formalization does **not** establish non-Gaussian optimality, an infinite-mode theorem, optimizer uniqueness, a closed-form optimizer, or the optional separately prescribed-total-parity strengthening.

## Frozen project identity

All **313 submitted project files**, including **308 Lean sources**, are preserved byte for byte. The protected inventory includes the root module, every Gaussian module, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `build_serial.py`, and the project's own README. Even the independently classified nonmaterial stale comment in `ThermalEntropy.lean` is unchanged. The internal package version in the immutable `lakefile.toml` is its original standalone-project version, not the repository release version.

The complete path/size/SHA-256 inventory, exact dependency revisions, root names and evidence identities are in [the source provenance record](../provenance/LEAN_FORMALIZATION_SOURCE.json). Every protected file also has an entry in [the source map](../provenance/SOURCE_MAP.json).

| Frozen evidence | SHA-256 | Recorded verdict |
| --- | --- | --- |
| Gaussian_MinPur_Lean_Formalization_Output.zip | `177f54de4e70fe08953b0d4b833e9987f5febf8d0eca4701c68a82ab9570faed` | FULL_FORMALIZATION_VERIFIED |
| Gaussian_MinPur_Lean_Independent_Verification_Output.zip | `f429b547e444f34792eab5be2fb6e3a88e79b940fab0e566bf35d24383824451` | INDEPENDENT_REPLAY_AND_SEMANTIC_AUDIT_PASS |

These large archives are not Git-tree contents. Their unchanged distribution as Release evidence assets requires separate privacy/security clearance. Frozen archive identity must never be represented by a sanitized or repackaged derivative.

## Trusted base and independent verification

Fresh independent root checks report only Lean's standard foundational dependencies **`propext`, `Classical.choice`, and `Quot.sound`**. No project-local mathematical axioms or proof holes were found.

A separate Codex run independently reproduced the project: all 308 Gaussian modules and 74 selected Physlib modules were rebuilt from source, ordinary `lake build` passed, and all 313 submitted files remained byte-identical. Official pinned upstream mathlib caches were reused; campaign-compiled Gaussian/Physlib objects were not used. Its targeted independent semantic audit found no substantive unresolved finding. The stale explanatory comment noted above was classified as nonmaterial.

The internal development record contains **three complete A–F cycles**, with the documented role/exposure qualifications. This is not a claim of three fully blind mutually independent audits. AI audit and kernel verification also do not constitute human expert review or journal peer review.

## Exact environment

| Component | Pin |
| --- | --- |
| Lean | 4.34.1 |
| Lake | 5.0.0-src+5045d00 |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Physlib | `af484f78ee0701290595f8bf892b157b10d64940` |

All 15 dependency revisions are committed in `formalization/lake-manifest.json`. Do not run `lake update`, regenerate the lock, or modify the project to adapt it to a newer toolchain. Elan selects the exact Lean release from `formalization/lean-toolchain`. Dependency software retains its own licenses; see [licensing](../LICENSING.md).

## Routine public CI and local equivalent

From a **fresh source-only checkout**, with Git, Python 3.12 and the official elan toolchain manager installed:

~~~sh
python scripts/verify_repository.py
python scripts/verify_lean_source.py --check-tracked
python scripts/test_lean_gates.py
python scripts/lean_ci.py --use-official-cache --check-tracked
~~~

The [dedicated Lean workflow](../.github/workflows/lean.yml) uses Ubuntu 24.04, full-SHA-pinned checkout/Python actions, read-only repository permissions, and an exact official elan release archive with a SHA-256 check. It disables implicit Lake cache downloads and Gaussian artifact-cache reads/writes through `LAKE_NO_CACHE=true`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_RESTORE_ARTIFACTS=false`, and an empty `LAKE_CACHE_DIR`. Inherited Lake/Lean/mathlib overrides are removed; each run gets private cache/configuration paths. `LEAN_NUM_THREADS=2` bounds the Lake runtime worker count consistently in CI and local runs; the frozen project also retains its per-module `-j1` Lean option. The optional explicit official mathlib cache command remains permitted. Before success, all **308 Gaussian modules must have actual `Built` records** in the fresh ordinary build; replayed or fetched records are insufficient. These controls follow the [exact pinned Lake cache settings](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Config/Env.lean) and [package cache-read rules](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Config/Monad.lean). Its script verifies the complete source inventory, checks every materialized dependency HEAD and clean tracked state, verifies exact Lean/Lake versions, obtains optional official pinned upstream caches, and runs ordinary **`lake build`**. Both exact root declarations are then checked and their individual trusted-base sets must equal the three standard dependencies above. Missing, duplicate or unrelated root reports fail; warnings and `sorryAx` also fail.

The source gate rejects executable `sorry`, `admit`, and project-local `axiom` tokens outside comments/strings. Negative controls exercise protected-byte changes, extra files, missing/wrong root output, unexpected axioms, inherited cache overrides and missing actual source-build coverage. A successful textual scan alone is not a proof; the actual source build and root checks are required.

Generated logs and probe files go in `.local/lean-ci/`, outside the protected project. The script refuses a pre-existing `formalization/.lake/build`; for a new replay, use a new checkout rather than reuse Gaussian proof products. Dependency caches are allowed, but their pinned source identity is checked. Passing routine CI requires fresh source compilation; it is not a claim that all of mathlib was rebuilt from source, that a new independent semantic audit occurred, or that the compiler/operating-system trusted computing base itself was formally verified.

For the more expensive serial source-rebuild procedure, the original protected `formalization/build_serial.py` remains available. To keep its generated evidence outside the project:

~~~sh
cd formalization
python build_serial.py --log-dir ../.local/lean-serial
~~~

That procedure builds Gaussian and the selected Physlib import closure module by module before ordinary `lake build`. It is distinct from routine public CI. Neither workflow extends the theorem's scope exclusions.
