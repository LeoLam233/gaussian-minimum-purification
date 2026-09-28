# v0.1.1 — A Mode Bound for Gaussian Entanglement of Purification

Release date: 28 September 2026.

This revision makes the original authors' prior statement more explicit in the manuscript, expert brief, README files and source notes. Windt, Jahn, Eisert and Hackl already state in Section 6.3 that matched auxiliary mode counts can be used without loss of generality. The manuscript's contribution is the explicit comparison across all finite Gaussian auxiliary sizes, including the selected-mode equality condition and fixed-size attainment. The theorem, proof argument and bibliography are unchanged from v0.1.

The diagnostic replay entry point now rejects an optimized Python interpreter and removes `PYTHONOPTIMIZE` from child processes. A regression check injects a deliberate entropy error and requires the verifier to detect it. The archived scientific scripts and supplementary reconstruction packets remain unchanged. Reproduction instructions explain how to replay the frozen v0.1 scripts safely.

The workflow now uses full-SHA-pinned checkout and Python setup actions whose metadata declares Node 24, and it selects Ubuntu 24.04. The [audit status](audits/STATUS.md) records subsequent AI audit findings, the reproduced diagnostics and the limits of each review. No independent human expert validation or journal peer review is claimed.

This release includes the revised eleven-page manuscript and two-page expert brief, both LaTeX sources, scientific diagnostics, source maps, licenses, and file-integrity metadata. The v0.1 tag and its attachments remain available at their original hashes. This v0.1.1 source archive corresponds to the v0.1.1 tag; the default branch can later contain further documentation edits.

Original code: MIT. Original paper and prose: CC BY 4.0. The two unchanged input packets retain the third-party attribution and license notices for their source papers.
