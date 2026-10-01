# v0.1.3 — Lean formalization and reproducibility integration

Release date: 1 October 2026. Baseline: v0.1.2 commit `f0d0ba959472bf4eda97319b8d79fe51461e0b60`, tree `91b29c15888b58caf088477fd8577f78a3e3a144`.

- Integrate the source-only verified Lean project without changing any of its 313 files, including 308 Lean sources.
- Add repository-level identity/provenance controls, reproducibility instructions and a dedicated public source-build workflow.
- Document exact bosonic/fermionic physical roots, all independently finite auxiliary sizes, actual matched-size attainment, and physical state/covariance/entropy semantic bridges.
- Record the separate Codex source rebuild and targeted semantic audit. Fresh root checks report only `propext`, `Classical.choice`, and `Quot.sound`; no project-local mathematical axioms or proof holes were found.
- Retain the explicit Apache-2.0 upstream proof attribution and all standalone-project bytes.

The mathematical theorem/proof is unchanged. Manuscript and expert brief remain v0.1.1; the preferred manuscript citation remains v0.1.1. This is a formal-verification/reproducibility layer, not a new manuscript revision. It makes no non-Gaussian, infinite-mode, uniqueness, closed-form-optimizer, or separately prescribed-total-parity claim. Internal A–F cycles retain their documented role/exposure qualifications. Human expert validation and journal peer review have not been performed.

The two frozen Lean evidence ZIPs are Release-only assets subject to an independent privacy/security gate; they are never committed to Git. Historical tags and assets retain their original bytes. See [the formalization guide](docs/LEAN_FORMALIZATION.md) and [licensing](LICENSING.md).

# v0.1.2 — documentation/audit-only release

Release date: 30 September 2026. This documentation/audit-only release derives from the approved post-stagec-rc1 against baseline `313c3e8ac67463388c36a4094a42f40aec8a3aa6`.

- Add curated Stage A/B/C roles, exposure limits and artifact hashes.
- Reconcile proof independence through the exact adapted-J hull/complement and spectrum/equality crosswalk.
- Clarify later review of selected supplementary nodes and limits of the original diagnostic scripts; preserve all frozen outcomes and payloads.
- Add compact architecture/common-core notes, including counterexamples to an overbroad deletion claim that the manuscript does not use.

The manuscript, expert brief and scientific scripts are unchanged. VERSION and the top-level citation identify repository v0.1.2; the preferred manuscript citation retains v0.1.1. RELEASE_METADATA separates the v0.1.2 release from the historical v0.1.1 release and approved integration RC. No human peer review or formal verification is claimed.

# v0.1.1 — A Mode Bound for Gaussian Entanglement of Purification

Release date: 28 September 2026.

This revision makes the original authors' prior statement more explicit in the manuscript, expert brief, README files and source notes. Windt, Jahn, Eisert and Hackl already state in Section 6.3 that matched auxiliary mode counts can be used without loss of generality. The manuscript's contribution is the explicit comparison across all finite Gaussian auxiliary sizes, including the selected-mode equality condition and fixed-size attainment. The theorem, proof argument and bibliography are unchanged from v0.1.

The diagnostic replay entry point now rejects an optimized Python interpreter and removes `PYTHONOPTIMIZE` from child processes. A regression check injects a deliberate entropy error and requires the verifier to detect it. The archived scientific scripts and supplementary reconstruction packets remain unchanged. Reproduction instructions explain how to replay the frozen v0.1 scripts safely.

The workflow now uses full-SHA-pinned checkout and Python setup actions whose metadata declares Node 24, and it selects Ubuntu 24.04. The [audit status](audits/STATUS.md) records subsequent AI audit findings, the reproduced diagnostics and the limits of each review. No independent human expert validation or journal peer review is claimed.

This release includes the revised eleven-page manuscript and two-page expert brief, both LaTeX sources, scientific diagnostics, source maps, licenses, and file-integrity metadata. The v0.1 tag and its attachments remain available at their original hashes. This v0.1.1 source archive corresponds to the v0.1.1 tag; the default branch can later contain further documentation edits.

Original code: MIT. Original paper and prose: CC BY 4.0. The two unchanged input packets retain the third-party attribution and license notices for their source papers.
