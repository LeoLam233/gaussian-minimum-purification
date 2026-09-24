# A Mode Bound for Gaussian Entanglement of Purification

**Dehao Lin**<br>
School of Physics, Sun Yat-sen University, Guangzhou, China<br>
lindh9@mail2.sysu.edu.cn

**Manuscript v0.1.** [Read the paper](paper/manuscript.pdf) · [Proof guide](docs/PROOF_GUIDE.md) · [Reproduce the checks](REPRODUCIBILITY.md) · [Evidence and audit status](audits/STATUS.md)

For a finite-mode bipartite Gaussian state, the paper proves that Gaussian entanglement of purification attains its minimum with as many auxiliary modes on each side as physical modes:

$$
E_P^{\mathrm G}(\rho_{AB})
=\min_{\substack{\psi_{ABA'B'}\ {\rm pure\ Gaussian},\ \psi_{AB}=\rho_{AB}\\
n_{A'}=n_A,\ n_{B'}=n_B}}S(\psi_{AA'}).
$$

The infimum on the left allows **all finite auxiliary mode counts**. The bosonic statement assumes a normal state with finite covariance; the fermionic statement concerns parity-invariant quasifree states, including pure factors, zero modes and degeneracies.

This is the mode-count assertion of Windt, Jahn, Eisert and Hackl's minimum purification conjecture. Their paper already states the matched-size restriction and gives a canonical construction. The present contribution supplies an explicit variational reduction from arbitrary finite auxiliary sizes and proves attainment. The introduction explains the relationship to the original assertion and construction; see [source positioning](provenance/SOURCES.md).

## The proof in one paragraph

An excess auxiliary mode can be selected so that transferring it across the purification cut does not increase entropy. At an attained minimum with a fixed auxiliary total, the entropy cannot decrease either. The equality case then forces the selected mode to be a pure factor, which can be removed. A separate bosonic argument prevents minimizing sequences from escaping to degenerate symplectic cuts. Iterating the removal and then matching the split proves the theorem.

The result does not establish optimality among non-Gaussian purifications, give a closed formula for the minimum, or guarantee global convergence of a local optimizer. It does not claim an infinite-mode or continuum extension.

## Start here

- [Manuscript PDF](paper/manuscript.pdf), [LaTeX source](paper/manuscript.tex), and [build instructions](paper/README.md).
- [Proof guide and the steps worth checking first](docs/PROOF_GUIDE.md).
- [Reproduction instructions](REPRODUCIBILITY.md) and [audit qualifications](audits/STATUS.md).
- [Source and artifact provenance](provenance/SOURCE_MAP.json), [archival boundary](provenance/ARCHIVAL_BOUNDARY.md), and [release notes](RELEASE_NOTES.md).
- [Author and AI contribution statements](AUTHORSHIP.md) and [citation metadata](CITATION.cff).

## Verify and reproduce

Python 3.12 was used for the recorded replays. From the repository root:

~~~sh
python scripts/verify_repository.py
python -m pip install -r requirements.txt
python scripts/reproduce.py
~~~

The reproduction command runs the six original verifiers and the separately written density-operator checks in fresh working directories. Generated results go under .local/; the versioned scripts and manuscript are left untouched.

These computations are finite diagnostics. The analytic proof carries the universal claim. Three AI reviews found no effective counterexample requiring a change to the main proof, but some external audit statistics could not be reproduced from the retained scripts; [their limitations are recorded](audits/STATUS.md). **Independent human expert validation and journal peer review have not been performed.**

## AI contribution and licensing

An AI workflow designed and assembled by the author autonomously selected the open problem and developed the proof. AI systems played the primary role in the derivation and computational checks, and other AI systems carried out adversarial reviews. AI assistance also contributed to exposition and repository preparation. These reviews are distinct from human peer review.

Original code is licensed under [MIT](LICENSE). The original manuscript and documentation are licensed under [CC BY 4.0](LICENSES/CC-BY-4.0.txt). See [licensing scope](LICENSING.md) for third-party exclusions. The full frozen research archive is retained separately; this repository is its documented, reproducible public-facing view.
