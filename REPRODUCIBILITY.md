# Reproduce the diagnostics and Lean formalization

The manuscript presents an analytic proof. This repository also includes its finite diagnostic checks and a separately written density-operator check, with source hashes tying them to the retained research and audit archives.

## Environment and commands

Use Python 3.12 and the dependency pins in requirements.txt. The recorded development environment used Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0 and mpmath 1.3.0. A separate virtual environment is suitable.

~~~sh
python scripts/verify_repository.py
python -m pip install -r requirements.txt
python scripts/reproduce.py
~~~

The standard-library verifier checks the repository manifest, current manuscript hashes, source-map hashes, citation metadata, and local Markdown links. It also verifies the full frozen 313-file Lean source identity. It ignores Git internals, .local/, .venv/, generated Lean build/evidence directories and Python bytecode caches; the dedicated tracked-file gate rejects committed proof products.

The reproduction entry point first requires Python assertions to be enabled, then verifies the repository, copies the scientific scripts into a new directory under .local/runs/, runs them there, saves stdout and generated JSON, and returns a nonzero status if a job fails. It sets common BLAS thread counts to one. Successful execution must also produce the expected PASS summary and case counts.

Run without `-O`, `-OO` or `PYTHONOPTIMIZE`: the archived scientific scripts contain assertions that Python removes in optimization mode. The current entry point rejects an optimized interpreter with exit code 2 and also removes `PYTHONOPTIMIZE` from child-process environments. The latter is necessary when the parent ignores the variable (for example, with `-E`) but its children would otherwise inherit it. Frozen v0.1 does not contain these safeguards; use an unoptimized interpreter and unset `PYTHONOPTIMIZE` when replaying that release.

The regression check `python scripts/test_replay_safety.py` verifies rejection of optimized invocation and deliberately injects a +1 nat error into the covariance entropy calculation in memory. The child verifier must fail at its entropy assertion, including when `PYTHONOPTIMIZE` was present in the parent environment. CI runs this check before the scientific suites.

To run one group:

~~~sh
python scripts/reproduce.py --suite original
python scripts/reproduce.py --suite independent
~~~

The original scientific files are not edited by this entry point. Running them directly in their versioned directories would rewrite outputs; use the entry point.

## What the checks do

| Group | Scope |
| --- | --- |
| Original six verifiers | Covariance compression, finite Fock representations, selected exact algebra, auxiliary orbit/boundary examples, a failed shortcut, and mutation checks. |
| Independent density checks | Four bosonic density-kernel examples with quadrature refinement; 32 fermionic density-matrix examples; 12 graded-cut and parity checks. The implementation does not import the original verifier code. |

Here, "independent" describes a separately written implementation within the AI research workflow. It does not mean independent human expert validation.

The original suite mixes exact finite algebra with ordinary and higher-precision numerical diagnostics. None is a complete formal certificate for the universal theorem. Floating-point agreement and successful quadrature refinement have their stated finite scope.

## Reference records

validation/reference/ contains the previously recorded successful logs and summaries. The independent JSON's local interpreter path is replaced by a disclosure-neutral marker; numerical fields are unchanged. The source map records the original and distributed hashes and that specific transformation.

validation/ASSEMBLY_REPLAY.json and validation/RC2_REPLAY.json retain the dated rc1 and rc2 replays. Each record describes the files current at its own execution time. The rc3 revision changes introductory prose and documentation; all scientific scripts remain byte-identical to those replayed in rc2, as recorded in provenance/AI_DISCLOSURE_UPDATE.json. Full output of a fresh local run is retained under .local/ and is not automatically committed. Platform-dependent floating-point output is not required to be byte-identical to earlier output; assertions, exit codes and generated-summary checks determine replay success.

The initial coarse-quadrature calculation and its subsequent refinement are retained together in the full review archive. The public check includes quadrature refinement.

## Build the manuscript

See [paper/README.md](paper/README.md). A rebuild writes to a new .local/ directory. The versioned PDF is not overwritten by the build command; an independently rebuilt PDF may differ in metadata bytes.

The GitHub Actions workflow verifies the manifest and runs the diagnostics when the repository is published. It selects `ubuntu-24.04` and pins the checkout and Python setup actions to full commit SHAs whose metadata declares Node 24. The runner image still receives updates; this is not a claim of byte-identical execution environments. Remote execution status is shown in the repository Actions tab; the dated local replay records do not claim a remote run.

## Independent derivation protocols

The [reconstruction directory](reproduction/README.md) contains the complete CR0 and MR1 input packets, three mathematical outputs and their provenance. These research runs are distinct from replaying the diagnostic scripts. The released proof does not use the supplementary results as premises. Later selected-node review and the separate Stage A/B/C records are described in that directory; historical campaigns are not automatically included in this replay.

## Diagnostic limitations clarified after Stage C

The original orbit examples start from orbit-generated extensions, so their reconstruction success does not establish that all extensions lie in that orbit. The endpoint support fixtures in the exact-geometry script start with a known pure eigenvector; they do not test the full implication from entropy equality. The original mutation suite supplies counterexamples to false mathematical statements, whereas `test_replay_safety.py` injects an actual entropy fault into a verifier. These are different checks.

Historical scripts and reference outputs are preserved byte for byte. Stage A/B/C supply additional tests and analytic reconstructions, summarized in [the assessment](audits/POST_STAGE_C.md), but their raw campaigns are retained separately and are not run by `scripts/reproduce.py`. A successful replay checks the retained suite, not the universal theorem, every historical campaign, or proof independence.

## Lean formalization added in v0.1.3

See [the formalization guide](docs/LEAN_FORMALIZATION.md) for exact physical root declarations, scope, trusted-base wording, all dependency pins and the distinction between the expensive independent serial rebuild and routine CI. The 313 submitted project files are immutable, including their original README and build script. All repository-specific controls live outside that project.

From a fresh source-only checkout with Git, Python 3.12 and official elan installed:

~~~sh
python scripts/verify_lean_source.py --check-tracked
python scripts/test_lean_gates.py
python scripts/lean_ci.py --use-official-cache --check-tracked
~~~

The last command selects Lean 4.34.1 / Lake 5.0.0-src+5045d00, verifies all exact dependency revisions, optionally reuses official upstream mathlib caches, compiles Gaussian sources with ordinary `lake build`, and checks both named physical roots and their individual foundational dependency sets. It refuses pre-existing Gaussian build products. It does not rebuild all mathlib sources or repeat an independent semantic audit. No submitted `sorry` or `admit` is permitted. Logs are generated under .local/lean-ci/. The public Lean workflow is separate from the existing finite diagnostic workflow; both must succeed on the exact release commit.
