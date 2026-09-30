# Additional results from the reconstruction attempts

**Status: supplementary; review coverage is claim-specific.** The original targeted reading and later Stage C examination of the mixed-mode reduction, gauge attainment and compression interfaces are recorded in [REVIEW_NOTES.md](REVIEW_NOTES.md). This is not a complete separate audit of every ancillary claim in this collection. The released manuscript does not depend on these results. No novelty or priority claim is made.

## A. Standard bounds and an exactly solvable family (CR0-1)

The first run rederived

$$
\tfrac12 I(A:B)\le E_P^{\mathrm G}(\rho_{AB})\le\min\{S(A),S(B)\}.
$$

It also treated states that, after local Gaussian transformations, are a pure correlated core tensored with independent local mixed states. The lower bound and a local-purification construction coincide for that family. These include pure and product cases. These facts and direct consequences of standard Gaussian theory are not presented as new results merely because a fresh AI run rederived them.

The run reformulated the remaining general step in terms of Gaussian Stinespring extensions and output-size compression, but did not prove that compression. See the [full original derivation](runs/CR0-1/RESULT.md) and the [infimum/attainment qualification](REVIEW_NOTES.md).

## B. Compression controlled by the mixed-mode count (CR0-2)

Let r be the number of mixed normal modes of the entire physical state AB: bosonic symplectic parameters strictly above 1, or fermionic normal-mode parameters strictly below 1, counted once per mode. It is not the Hilbert-space rank of the density operator.

The second run claims an explicit non-increasing-entropy reduction of any finite Gaussian purification to at most r auxiliary modes on each side, followed by pure-mode padding if necessary:

$$
E_P^{\mathrm G}(\rho_{AB})=\min_{\Psi\in\mathcal P_{r,r}}S(\Psi_{AA'}).
$$

Its bosonic construction uses a Schur-complement elimination and Gaussian displacement mixing. Its fermionic construction uses two pure covariance candidates and entropy concavity. The full formulas and boundary cases are in [CR0-2](runs/CR0-2/RESULT.md).

This does not by itself establish the general matched-size result. For example, n_A=n_B=1 can have r=2, leaving a comparison between (2,2) and (1,1). The run solves the subdomain r<=min(n_A,n_B), but preserves PARTIAL for the general task. The fermionic domain permits both definite pure-state total parities.

## C. A direct fixed-size attainment route (CR0-2, then MR1-1)

For bosons at a fixed finite auxiliary split, the runs give a shorter alternative to the manuscript's auxiliary-cut argument:

1. Choose a minimizing sequence with bounded cut entropy and normalize auxiliary first moments.
2. Williamson-normalize A' and B' separately by local Gaussian unitaries.
3. Araki–Lieb and global purity bound both auxiliary marginal entropies. The bosonic one-mode entropy is increasing and unbounded, so every normalized auxiliary covariance diagonal entry is bounded.
4. Positivity bounds every cross entry by `|V_ij|^2 <= V_ii V_jj`. Extract a finite matrix limit.
5. The physical marginal and polynomial purity identity survive. Purity makes the limit invertible; positivity makes it an admissible finite covariance. Entropy continuity yields a minimum.

The first occurrence in these records is [CR0-2, section 6.2](runs/CR0-2/RESULT.md). This route was then explicitly supplied in the MR1 framework and expanded in [MR1-1, section 7](runs/MR1-1/RESULT.md). Its later reconstruction is not a second independent discovery of the idea.

The fermionic counterpart directly uses the closed, bounded set of pure covariances with a fixed physical block. These alternative arguments may help a future revision, but have not replaced the released manuscript's attainment proof.

## D. A metric formulation of bosonic compression (MR1-1)

The guided run writes, for V=SDS^T,

$$
J=S^{-T}(-\Omega)S^T,\quad g=\Omega J=SS^T,\quad K=g^{-1}V.
$$

The selected auxiliary plane is J-invariant; its physical symplectic complement is also its g-orthogonal complement. The actual retained symplectic spectrum is then the spectrum of a g-Hermitian compression. The complete argument and equality condition are in [MR1-1, section 5](runs/MR1-1/RESULT.md). This is another presentation of the supplied compression architecture, not a new theorem added to v0.1.
