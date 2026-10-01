# Audit and evidence status

## Lean formalization integration: 1 October 2026

The immutable source-only [Lean project](../formalization/README.md) is added for repository v0.1.3. Its [provenance](../provenance/LEAN_FORMALIZATION_SOURCE.json) binds all 313 project files (308 Lean sources) to the frozen formalization archive and the separate independent verification archive. The recorded verdicts are FULL_FORMALIZATION_VERIFIED and INDEPENDENT_REPLAY_AND_SEMANTIC_AUDIT_PASS.

The separate Codex verification rebuilt 308 Gaussian and 74 selected Physlib modules from source, completed ordinary `lake build`, preserved the bytes of all 313 submitted files, and found no substantive unresolved issue in its targeted semantic audit. Fresh physical-root checks report only `propext`, `Classical.choice`, and `Quot.sound`; no project-local mathematical axioms or proof holes were found. Official pinned upstream mathlib caches were reused. The internal campaign records three complete A–F cycles with documented role/exposure qualifications, not three fully blind mutually independent audits.

The [formalization guide](../docs/LEAN_FORMALIZATION.md) states exact roots, finite-mode Gaussian scope, semantic bridges and exclusions. The nonmaterial stale ThermalEntropy comment is retained unchanged. The manuscript theorem/proof and v0.1.1 manuscript/brief are unchanged. Formal verification and AI audits remain distinct from independent human expert review or journal peer review.

## Historical Stage A/B/C assessment: 30 September 2026

The [Stage A/B/C integration assessment](POST_STAGE_C.md) adds a reported blind complete derivation, hostile manuscript scrutiny and cross-proof dependency analysis. Multiple complete derivations use partially independent global reduction and attainment mechanisms while sharing a nontrivial adapted-J compression/spectral core. No new load-bearing defect was found in the checked routes. The manuscript and expert brief remain v0.1.1 and are unchanged by the v0.1.2 documentation release.

Stage B and Stage C are audits, MR1 is method-guided, and the CR0 outcomes remain PARTIAL. Review of selected supplementary nodes does not certify every ancillary result. These Stage A/B/C AI reviews are not independent human validation, journal peer review or proof-assistant formalization; the later Lean evidence is described separately above. [Evidence identities and exposure limits](../provenance/POST_STAGE_C.json) distinguish reported provenance from authenticated bytes.

## Historical manuscript reviews: 24–25 September 2026

Three AI reports examined the 24 September 2026 manuscript. Their assessment informed the 25 September revision. The released manuscript also contains a subsequent editorial revision of one introductory attribution paragraph (rc2) and a brief AI-workflow disclosure in the introduction (rc3). This paragraph records the early review sequence; later manuscript and cross-proof audits are described above by their actual scope.

| Review or computation | Scope and retained evidence |
| --- | --- |
| Review A: A1V2, fresh context | Conducted without the research conversation, using the same model as the coordinating system. The review re-derived key steps, reran the six original scripts, and supplied separate density-operator and graded-subsystem checks. |
| Review B: ds4.1Flash | The report identified no fatal mathematical flaw and reported 4000+4000+480 successful tests. The retained scripts appear to be an earlier revision and do not reproduce those final counts. The counts are therefore treated as report-level evidence; corrected interactive runs were not independently recovered. |
| Review C: additional AI report | Follow-up checks reproduced 480 generic compression cases and two bosonic orbit constructions. Two issues in the retained implementation were identified: the Jacobian used I rather than 0 in the fixed physical block, and the fermion entropy routine mishandled zero and pure endpoints. These implementation issues did not produce a manuscript counterexample. |
| Follow-up tangent calculation | A separate driver with the corrected fixed-marginal tangent gave ranks 10, 20, 21 and 36. This is a local diagnostic; Appendix A provides the analytic orbit argument. |
| Nonlinear searches | Finite local searches were not certified as global optimizations. Equal padded candidate values and local search outcomes are supporting diagnostics. |
| Human and journal review | Not performed. |

The assessed objections did not require a change to the central proof. This is an assessment of the available arguments and calculations, within the limits above.

## Changes following review

The manuscript credits the earlier formulation and mode-count statement, distinguishes canonical construction from comparison over all finite extensions, and uses the published section and equation numbering. It also makes the fixed-parity empty-system exception and the inverse-transpose auxiliary transformation explicit.

The rc2 editorial revision retains this attribution and contribution scope while describing the relationship to the earlier work in more direct, neutral prose. The rc3 revision adds a one-sentence AI-workflow disclosure in the introduction and retains the full end-of-paper statement. The theorem, proof, bibliography and scientific verification code are unchanged by these revisions.

## Public computational evidence

The runnable checks are the six original verifiers and Review A's separately written density-operator implementation. Earlier successful records and repository-entry-point replay records are included. The full review archives, including intermediate implementations, are retained separately; implementations with the issues described above are not included in the default verification suite.

Finite computations and AI review provide diagnostic evidence. They do not constitute a formal verification of the universal theorem or human peer review.

## Literature and source status

The recorded public-literature searches found no matching proof. The earlier paper's statement is credited, and no unverified third-party AI repository was identified as a premise of the proof. This is a dated search outcome, not an absolute priority claim. Repository preparation and the editorial revision did not conduct a new novelty audit.

The [archive map](../provenance/ARCHIVAL_BOUNDARY.md) identifies the retained review reports and their hashes.

## Reconstruction records added for public v0.1

Two problem-only derivation attempts remained PARTIAL. A later method-guided rederivation claimed a complete proof; targeted post-freeze reading identified no load-bearing gap in its eight requested nodes. These outcomes and qualifications are recorded in [reproduction/README.md](../reproduction/README.md).

At the v0.1 reconstruction release, the [additional results](../reproduction/EXTRA_RESULTS.md) had received targeted reading, not a separate complete adversarial audit. Later selected-node coverage is recorded in the current assessment and [review notes](../reproduction/REVIEW_NOTES.md). They remain outside the manuscript's proof dependencies. The scientific scripts and proof argument are unchanged from rc3; v0.1.1 made editorial manuscript changes. Historical publication notices retain their original scope.

## Post-release replay safety check (28 September 2026)

An additional AI audit dated 27 September reviewed the v0.1 tag and the then-current `main` separately, checked the selected-mode equality argument, and ran separately written compression and auxiliary-orbit diagnostics. It reported no P0/P1 mathematical defect or identified prior complete proof. Its local searches and finite novelty search remain limited evidence; neither establishes the theorem or a priority claim. The v0.1 source ZIP correctly represents the v0.1 tag rather than later `main` documentation edits. The v0.1.1 release again binds its source ZIP to its own tag.

A further AI review found that Python optimization removes assertions used by several archived scientific verifiers. Its fault-injection probe was reproduced locally: adding 1 nat to the covariance entropy calculation caused an assertion failure in normal mode, but the optimized verifier returned success and printed PASS. This is a replay-safety defect; it does not supply a counterexample to the analytic proof or show that the default CI run used optimization.

The reproduction entry point now refuses an optimized interpreter and removes `PYTHONOPTIMIZE` from child environments. The [regression tests](../scripts/test_replay_safety.py) exercise both protections using the actual entropy verifier, and CI runs them before the diagnostic suites. The scientific source files remain unchanged. The frozen v0.1 tag and release attachments retain the earlier entry point; the [reproduction instructions](../REPRODUCIBILITY.md) explain how to run them with assertions enabled.

The supplied report and evidence archive were checked against their supplied SHA-256 values, and all 55 entries in the archive's internal manifest matched. Its additional independent checks were also rerun. That review did not acquire Release binaries or a full Git clone, so its coverage does not include those binaries, PDF appearance, or the complete history. It reported no P0/P1 mathematical defect within the proof it read. This remains AI-based checking, not human expert validation.

A subsequent supplied report confirmed the same optimization issue and identified a CI maintenance issue: the previously pinned actions declared Node 20 while the platform ran them on Node 24. Its archive contained 74 files, including a manifest with 73 verified entries. Its separately written determinant diagnostic was rerun successfully for 520 covariance/commutator pairs, an exact rational boundary family and high-precision entropy evaluations. These computations concern the stated boundary mechanism, not an independent proof of the full theorem. This report likewise did not acquire Release binaries or inspect the rendered PDFs.

The workflow now pins [checkout v7.0.1](https://github.com/actions/checkout/releases/tag/v7.0.1) and [setup-python v7.0.0](https://github.com/actions/setup-python/releases/tag/v7.0.0) by full commit SHA; both action metadata files declare Node 24. It selects `ubuntu-24.04` instead of the migrating `ubuntu-latest` label. This maintenance change does not alter the manuscript or scientific scripts. Its hosted execution must be assessed from a CI run of the updated commit, not inferred from the earlier successful runs.
