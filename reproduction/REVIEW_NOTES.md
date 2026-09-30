# Post-freeze review qualifications

The following original sections summarize the targeted AI reading available when the CR0/MR1 records were first projected publicly. Their historical scope was **not separately adversarially audited**. Later coverage is recorded in the dated addendum below. Neither stage is human peer review or a formal proof certificate.

## CR0-1

The partial outcome is retained. The report's section 4 describes a pointwise non-increasing-entropy replacement as equivalent to equality of infima. Without attainment, that equivalence needs an epsilon: equality of infima guarantees a matched candidate within any positive epsilon, not necessarily an exactly no-worse candidate for every original state. The stronger pointwise statement is sufficient. With an attained matched minimum the distinction disappears. This qualification does not turn the report into either a proof of the general theorem or a counterexample.

The finite local numerical searches were not certified as global optimizations or replayed in this targeted review. Their outputs are not used to establish the general comparison.

## CR0-2

Targeted reading checked the correlation-block rank, the proposed bosonic and fermionic elimination identities, and the direct fixed-size attainment argument. No load-bearing gap was identified in those checked steps. The general comparison between the claimed (r,r) bound and the matched split remained unresolved in the original run. Its diagnostics were not replayed in this review.

## MR1-1

Targeted reading covered G0, F1, F2, B1, B2, A_F, A_B and R. In the specified domain it found the argument closed without a load-bearing gap: the actual reduced covariances were identified with the Hermitian compressions, the equality cases were proved separately, and fixed-size attainment preceded deletion at an optimum. This assessment does not enlarge the scope to every auxiliary claim in the manuscript.

A small expository addition would make G0 fully explicit: the bosonic canonical-purification block has positive ordinary eigenvalues `nu +/- sqrt(nu^2-1)`, in addition to satisfying the purity identity. This is immediate from the displayed block, not a remaining research obligation.

The returned diagnostic contained one case per statistics and was read but not replayed in the receiving environment because SciPy was unavailable. Separately written NumPy spot checks covered 26 cases of physical compression, trace identities and constructed equality cases. They passed at floating-point precision; they do not establish universal validity or attainment and do not constitute a separate adversarial audit.

## Integrity and access limitations

All three received archives passed their retained manifest and result-file checks, and the separately supplied result files matched the corresponding archived payloads. The original input manifests matched the prepared packets. These checks bind received documents to their frozen records; they cannot certify unlogged accesses or technical isolation.

Early logging gaps and the disclosed output-directory/cache deviations are recorded in [RUNS.json](RUNS.json). MR1's first freeze failed on an automatically generated input bytecode cache; after cleanup, input verification and final freezing succeeded. The records do not show external proof material introduced through those deviations. Complete system-level access traces were not available.

## Addendum: Stage C assessment, 30 September 2026

Both Stage C records examined the manuscript, Stage A and MR1 routes, with Stage B's audit and the CR0 records available. Their analytic reconstructions address MR1's physical subsystem spectrum, exact rigidity, full-covariance bosonic attainment and global transfer/deletion. They also revisit CR0-2's mixed-mode-count reduction and fixed-size attainment, identifying the remaining original sidewise bottleneck. The integration review checked the decisive shared interfaces and the different global/attainment mechanisms; no new load-bearing defect was found there.

CR0-1 and CR0-2 remain PARTIAL for the full target. MR1 received the method architecture, including the gauge-attainment idea already present in CR0-2. Later scrutiny does not make it blind. The initial public notices and original run objects remain historical records, with this addendum recording the changed review coverage.

This selected-node coverage does not assert a complete separate audit of every bound, subclass, optional argument or historical numerical campaign in EXTRA_RESULTS or the raw records. Stage C expands some standard/expository premises in its own reconstruction; those expansions are not attributed retroactively to the original texts. See [Stage A/B/C assessment](../audits/POST_STAGE_C.md) and [proof architectures](../docs/PROOF_ARCHITECTURES.md).
