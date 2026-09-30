# Stage A/B/C evidence assessment

Assessment date: 30 September 2026. This is a curated review of the supplied frozen records against repository baseline `313c3e8ac67463388c36a4094a42f40aec8a3aa6`. The manuscript and its proof are unchanged. Run names, exposure statements and original verdicts are reported records; their labels are not mathematical premises.

## What the evidence adds

| Record | Role and information exposure | Material contribution | Qualification |
|---|---|---|---|
| Stage A | Reported blind/problem-only derivation; no manuscript, method framework or earlier verdicts before freeze | Whole-subsystem compression, a finite size cap, fixed-size attainment and deletion from both sides of a global optimizer | Frozen outcome `CLAIMED_PROOF`. Its global architecture differs from the manuscript; its adapted-J compression core overlaps. Isolation was not technically authenticated. |
| Stage B | Hostile manuscript audit; reportedly withheld Stage A | Reconstructed the manuscript's compression, equality, orbit, attainment and reduction interfaces; identified diagnostic weaknesses | An audit, not another complete derivation. Its own ledger retained a conditional standard Gaussian-formalism premise (EXT.4). |
| Stage C, Sol record | Cross-proof audit with manuscript, A/B, CR0 and MR1 evidence | Reconstructed the routes and attacked their physical subsystem/spectrum bridge | Describes two foundations at a broader architectural granularity. Its stronger assertion of no shared load-bearing compression lemma is not retained here. |
| Stage C, Pro record | Cross-proof audit of the same evidence pool | Identified the exact hull/complement duality and shared equality core; supplied explicit counterexamples to dropping the selection hypothesis | Describes three derivation artifacts with a shared compression foundation. This is a finer dependency classification, not a model vote. |

The manuscript, Stage A and MR1 contain complete analytic routes for the finite-mode matched-size value and attainment claims. The integration review reconstructed the selection/spectrum/equality interfaces and the different attainment/global reductions and found no new load-bearing defect. **Multiple complete derivations use partially independent global reduction and attainment mechanisms while sharing a nontrivial adapted-J compression/spectral core.** See [proof architectures](../docs/PROOF_ARCHITECTURES.md) and [common core](../docs/COMMON_CORE.md).

MR1 was method-guided: its compression/transfer architecture and the direct bosonic attainment route were disclosed before execution. The latter already appears in CR0-2. MR1 is not blind discovery. CR0-1 and CR0-2 retain their original `PARTIAL` outcomes. Stage B and both Stage C records are mathematical audits; they are not counted as additional proofs.

## What was reconciled mathematically

Stage A's spectral-half hull is `A+JA`. The selected mode in the manuscript and MR1 lies in its physical complement, `(A+JA)^perp=C intersect JC`. For bosons the complement is symplectic, and both presentations use the same positive-metric Hermitian compression after identifying the actual restricted covariance and commutator. Fermions use the corresponding orthogonal restriction. Their equality arguments meet at positivity of the endpoint operator, followed by pure-marginal factorization.

Different global reductions and attainment proofs remain useful. The manuscript uses fixed-total transfer/deletion with orbit/cut attainment; Stage A obtains a finite cap and then compresses both sides of one global optimizer; MR1 uses a bounded full-covariance limit for bosonic attainment. The [architecture note](../docs/PROOF_ARCHITECTURES.md) states exactly which arguments are shared.

Exact counterexamples disprove the stronger assertion that arbitrary entropy-preserving deletion removes a pure mode. They fail the actual adapted-J selection hypothesis, which the manuscript already states. Likewise, near equality does not authorize exact deletion. No manuscript repair follows from either observation.

One Stage B fixture discussion suggests uniqueness of the available line when `c-a=1`. That is not a general fact: product normal covariances can have `C intersect JC=C` with more than one complex line. The actual compression lemma requires neither uniqueness nor purity before equality. This qualification does not invalidate Stage B's reported fixture counts.

## Diagnostic scope

Source inspection supports Stage B's main qualifications:

- `verify_orbit_and_boundary.py` generates extensions inside the orbit before reconstructing them; those examples do not establish completeness over all extensions. Appendix A supplies the analytic proof.
- The endpoint support checks in `verify_exact_geometry.py` start with a known pure eigenvector. They check the fixture, not the general implication from entropy equality.
- `verify_mutations.py` tests counterexamples to false mathematical variants. It is distinct from injecting faults into a verifier. The existing replay-safety regression test does inject an entropy fault.
- Finite sampled spectra, squeezing ranges, density checks and local optimizations do not prove universal statements or global optimality.

The original scientific scripts and historical logs remain unchanged. Stage A/B/C contain additional implementations and destructive tests, but their campaigns are not included in the default repository replay and were not all rerun in the integration review. Current replay instructions describe the retained suite's actual scope.

## Integrity, access and external validation

The integration package, nested manifests/receipts and duplicate report payloads were checked. The packet's 11-page manuscript reading copy differs in bytes from the repository PDF; text comparison and the repository LaTeX support the mathematical correspondence, not binary identity. Archive/report/input SHA-256 values and exact member locators are in [the evidence registry](../provenance/POST_STAGE_C.json).

Large frozen archives remain outside the public tree under the existing [archival boundary](../provenance/ARCHIVAL_BOUNDARY.md). A fingerprint identifies bytes if an archive is supplied; it does not provide public access or authenticate model identity, unlogged access, mathematical correctness or a trusted timestamp. Some older raw review records remain unavailable in the supplied material.

No independent human expert validation, journal peer review or proof-assistant formalization is claimed. No new literature/priority search was performed. Later review of selected CR0/MR1 nodes does not certify every ancillary claim in the supplementary collection; [review coverage](../reproduction/REVIEW_NOTES.md) is recorded separately.
