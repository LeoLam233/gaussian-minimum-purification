# Proof architectures and their overlap

This navigation note compares the unchanged [manuscript](../paper/manuscript.pdf), the frozen Stage A derivation and the public [MR1 derivation](../reproduction/runs/MR1-1/RESULT.md). Source identities and locators are in [POST_STAGE_C.json](../provenance/POST_STAGE_C.json). It does not replace any original proof or alter historical outcomes.

| Component | Manuscript | Stage A | MR1 |
|---|---|---|---|
| Local compression | Select one auxiliary complex line in `C intersect JC` | Retain the whole spectral-half hull `A+JA`, at most twice the physical-side mode count | Execute the disclosed one-line construction |
| Exact equality | Endpoint trace and positivity force selected mode pure | Ky Fan equality forces discarded complement pure | Endpoint trace and positivity |
| Bosonic attainment | Complete auxiliary orbit, cut parametrization, entropy divergence at degenerate symplectic cuts | Gauge-normalize B', take a bounded ABB' marginal limit, preserve a closed mixed-mode rank bound, repurify | Gauge-normalize both auxiliaries, take a bounded full-covariance limit preserving polynomial purity |
| Fermionic attainment | Compact cut Grassmannian | Compact pure-covariance feasible set | Compact pure-covariance feasible set |
| Global reduction | Exact fixed-total optimizer → transfer → equality → delete → induct total; then match split | Pointwise finite cap → global optimizer → equality-compress both original sides → delete complements → pad | Same fixed-total architecture as manuscript |
| Exposure | Original proof artifact | Reported blind/problem-only | Method-guided; architecture and gauge-attainment route supplied |

Stage A's intermediate cap is `(n_A,2n_A+n_B)`. It is used to obtain one global optimizer, not asserted to be the final matched bound. Its optional extreme-point existence argument is another existence branch, not an additional complete proof avoiding compression. MR1's gauge route first appears in CR0-2 and was disclosed to MR1; a fresh execution is not a second discovery of that idea.

## The exact crosswalk

On the real coefficient space `L=A direct_sum C`, let J be adapted to the covariance. Use the Euclidean complement for fermions and the symplectic complement for bosons. Since J preserves the relevant form,

$$
(A+JA)^\perp=A^\perp\cap(JA)^\perp=C\cap JC.
$$

The projections onto J's complex spectral halves are `(I±iJ)/2`. Their images of the complexified A span exactly the complexification of `A+JA`. Thus Stage A retains the minimal J-invariant hull of A, while the manuscript and MR1 select a line in its complementary auxiliary space. In a fermionic zero kernel, match the allowed choice of J before comparing the constructions.

The amount compressed differs, but the spectrum/equality mechanism is shared. The bosonic positive spectral-half metric is the same adapted metric `g=Omega J`; its generalized Ritz values equal the physical restricted symplectic spectrum. For fermions, the upper correlation-half operator is `(I+K)/2` when `Gamma=JK`. Arbitrary-codimension interlacing follows from the same min–max principle, or successive J-invariant hyperplane restrictions. At equality, positivity forces the entire discarded subspace to the pure endpoint. See [common core](COMMON_CORE.md).

## How much independence is justified

The Stage C reports count “foundations” differently: one emphasizes different compression propositions and global architectures; the other merges their underlying selection, spectrum and equality arguments. The exact crosswalk supports the deeper overlap while preserving the different global and attainment mechanisms. A failure specific to the manuscript's orbit/cut argument would not automatically refute Stage A's rank-limit argument, but a failure of the shared actual-subsystem spectrum bridge would affect all these routes.

**Multiple complete derivations use partially independent global reduction and attainment mechanisms while sharing a nontrivial adapted-J compression/spectral core.** A count of fully independent proofs is not assigned.

Stage B is a hostile manuscript audit. Stage C compares proofs and attacks shared assumptions. They add scrutiny and local reconstructions, not additional separately counted proof artifacts. CR0-1/CR0-2 remain partial for the full matched theorem. Their `(r,r)` or special-case results must not be relabeled as general sidewise closure.
