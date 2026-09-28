# A Mode Bound for Gaussian Entanglement of Purification

**Public release v0.1.1.** [Read the paper](paper/manuscript.pdf) · [Proof guide](docs/PROOF_GUIDE.md) · [Reproduce the checks](REPRODUCIBILITY.md) · [Evidence and audit status](audits/STATUS.md)

For a finite-mode bipartite Gaussian state, the paper proves that the Gaussian entanglement of purification has a minimum attained by a pure Gaussian purification with **the same number of auxiliary modes as physical modes on each respective side**. The optimization allows arbitrary finite auxiliary mode counts; the matched counts suffice. The bosonic statement assumes a normal state with finite covariance, and the fermionic statement concerns parity-invariant quasifree states, including pure factors, zero modes and degeneracies.

This establishes the mode-count assertion of the minimum purification conjecture formulated by Windt, Jahn, Eisert and Hackl. Their Section 6.3 explicitly states that auxiliary mode counts may be matched to the physical counts without loss of generality, and develops a canonical purification and analytical bounds. Building on these results, this work gives an explicit reduction across arbitrary finite auxiliary sizes and proves attainment; see [source positioning](provenance/SOURCES.md).

**AI-assisted research:** an author-designed AI workflow selected the problem and developed the proof; other AI systems performed adversarial reviews. See [the contribution statement](AUTHORSHIP.md).

## The proof in one paragraph

An excess auxiliary mode can be selected so that transferring it across the purification cut does not increase entropy. At an attained minimum with a fixed auxiliary total, the entropy cannot decrease either. The equality case then forces the selected mode to be a pure factor, which can be removed. A separate bosonic argument prevents minimizing sequences from escaping to degenerate symplectic cuts. Iterating the removal and then matching the split proves the theorem.

The result does not establish optimality among non-Gaussian purifications, give a closed formula for the minimum, or guarantee global convergence of a local optimizer. It does not claim an infinite-mode or continuum extension.

## Start here

- [Manuscript PDF](paper/manuscript.pdf), [LaTeX source](paper/manuscript.tex), and [build instructions](paper/README.md).
- [Two-page expert brief](docs/expert-brief/expert_brief.pdf) and [proof guide](docs/PROOF_GUIDE.md).
- [Independent-context attempts and method-guided rederivation](reproduction/README.md), with [additional results not separately audited](reproduction/EXTRA_RESULTS.md).
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

These computations are finite diagnostics. The analytic proof carries the universal claim. The initial three AI reviews and subsequent AI audit reports were considered alongside checks of their supporting calculations; [their scope and reproducibility limits are recorded](audits/STATUS.md). **Independent human expert validation and journal peer review have not been performed.**

## Reconstruction records and additional results

Two problem-only AI attempts returned PARTIAL. A later method-guided attempt returned CLAIMED_PROOF; targeted post-freeze reading found no load-bearing gap. This was reconstruction with a supplied method architecture, not blind discovery. The two earlier outcomes remain PARTIAL.

The complete input packets and mathematical outputs are in [reproduction/](reproduction/README.md). Alternative arguments and partial results are explicitly marked **not separately adversarially audited** and are not used as premises of the released manuscript. The original scientific scripts are unchanged from rc3. The v0.1.1 manuscript contains a documented editorial attribution revision; its proof statements and arguments are unchanged.

## AI contribution and licensing

An AI workflow designed and assembled by the author autonomously selected the open problem and developed the proof. AI systems played the primary role in the derivation and computational checks, and other AI systems carried out adversarial reviews. AI assistance also contributed to exposition and repository preparation. These reviews are distinct from human peer review.

Original code is licensed under [MIT](LICENSE). The original manuscript and documentation are licensed under [CC BY 4.0](LICENSES/CC-BY-4.0.txt). See [licensing scope](LICENSING.md) for third-party exclusions. The full research archive is retained separately; this repository provides the manuscript, runnable checks and a documented [public/private boundary](provenance/ARCHIVAL_BOUNDARY.md). The [rc2 editorial record](provenance/EDITORIAL_CHANGES.json) and [rc3 AI disclosure record](provenance/AI_DISCLOSURE_UPDATE.json) document the introductory wording changes; the mathematical argument and scientific scripts are unchanged.
