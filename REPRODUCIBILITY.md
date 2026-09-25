# Reproduce the diagnostics

The manuscript presents an analytic proof. This repository also includes its finite diagnostic checks and a separately written density-operator check, with source hashes tying them to the retained research and audit archives.

## Environment and commands

Use Python 3.12 and the dependency pins in requirements.txt. The recorded development environment used Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0 and mpmath 1.3.0. A separate virtual environment is suitable.

~~~sh
python scripts/verify_repository.py
python -m pip install -r requirements.txt
python scripts/reproduce.py
~~~

The standard-library verifier checks the repository manifest, current manuscript hashes, source-map hashes, citation metadata, and local Markdown links. It ignores Git internals, .local/, .venv/ and Python bytecode caches.

The reproduction entry point verifies the repository first, copies the scientific scripts into a new directory under .local/runs/, runs them there, saves stdout and generated JSON, and returns a nonzero status if a job fails. It sets common BLAS thread counts to one and does not silently accept failed assertions. Successful execution must also produce the expected PASS summary and case counts.

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

The original suite mixes exact finite algebra with ordinary and higher-precision numerical diagnostics. None is a complete formal certificate for the universal theorem. Floating-point agreement and successful quadrature refinement have their stated finite scope.

## Reference records

validation/reference/ contains the previously recorded successful logs and summaries. The independent JSON's local interpreter path is replaced by a disclosure-neutral marker; numerical fields are unchanged. The source map records the original and distributed hashes and that specific transformation.

validation/ASSEMBLY_REPLAY.json and validation/RC2_REPLAY.json retain the dated rc1 and rc2 replays. Each record describes the files current at its own execution time. The rc3 revision changes introductory prose and documentation; all scientific scripts remain byte-identical to those replayed in rc2, as recorded in provenance/AI_DISCLOSURE_UPDATE.json. Full output of a fresh local run is retained under .local/ and is not automatically committed. Platform-dependent floating-point output is not required to be byte-identical to earlier output; assertions, exit codes and generated-summary checks determine replay success.

The initial coarse-quadrature calculation and its subsequent refinement are retained together in the full review archive. The public check includes quadrature refinement.

## Build the manuscript

See [paper/README.md](paper/README.md). A rebuild writes to a new .local/ directory. The versioned PDF is not overwritten by the build command; an independently rebuilt PDF may differ in metadata bytes.

The GitHub Actions workflow verifies the manifest and runs the diagnostics when the repository is published. Remote execution status is shown in the repository Actions tab; the dated local replay records do not claim a remote run.

## Independent derivation protocols

The [reconstruction directory](reproduction/README.md) contains the complete CR0 and MR1 input packets, three mathematical outputs and their provenance. These research runs are distinct from replaying the diagnostic scripts. The released proof does not use the unaudited additional results as premises.
