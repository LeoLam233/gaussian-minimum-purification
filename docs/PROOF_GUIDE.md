# A short guide to checking the proof

The central statement is Theorem 2.1 of the [manuscript](../paper/manuscript.pdf). The optimization is over pure Gaussian extensions of a fixed finite-mode physical state and over every finite auxiliary size. The theorem proves existence of an optimum with the two auxiliary counts individually matched to their physical counterparts.

## The key step: equality turns transfer into removal

Lemma 3.1 considers a mixed Gaussian state on $X$ and $C$, with $a$ physical modes and $c>a$ auxiliary modes. A compatible complex structure $J$ on the joint coefficient space gives

$$\dim_{\mathbb R}(\mathcal C\cap J\mathcal C)\ge 2(c-a)>0.$$

Choose a complex line $P$ inside this intersection. Its complement is Euclidean for fermions and symplectic for bosons. In suitable coordinates, restriction to that complement is a Hermitian compression. Interlacing and the appropriate entropy monotonicity give

$$S(X\widetilde C)\le S(XC).$$

The equality statement concerns **the mode selected by this construction**: equality holds exactly when $P$ is a pure product factor. This is stronger than the entropy inequality alone. The trace identity and positivity force the selected line into a pure covariance block with no cross block.

Now take a minimum at a fixed auxiliary total $M$, minimizing over all assignments to $A'$ and $B'$. If one side has an excess mode, use the lemma to transfer it to the other side. The physical marginal and $M$ do not change. The entropy cannot increase by compression and cannot decrease by global minimality at that $M$. Equality therefore holds; $P$ is pure even as a marginal of the full extension, so it can be removed. Padding in the other direction costs no entropy. Thus $e_M=e_{M-1}$ for $M>n_A+n_B$. At the remaining total $n_A+n_B$, transfers reach the matched split.

## Why the fixed-total minimum exists

Propositions 4.1 and 4.2 first identify the full auxiliary orbit and the exact cut space. Appendix A gives a covariance proof, separating pure physical modes before taking any inverse.

For fermions the relevant Grassmannian is compact. For bosons, admissible symplectic cuts form an open subset of a compact Grassmannian. The proof bounds the largest restricted symplectic eigenvalue below by a fixed positive covariance bound divided by the smallest singular value of the restricted symplectic form. Approaching a degenerate cut makes entropy diverge. Finite-entropy sublevels therefore stay away from that boundary, yielding attainment.

## Checks with the greatest value

| Location | Question to check |
| --- | --- |
| Sections 3.1–3.2, pages 4–5 | Are the two interlacing directions correct, and does equality really force a decoupled pure mode? |
| Appendix A, page 9 | Does the row-frame completion cover every extension, including decoupled pure physical factors? For bosons, the covariance transformation is the inverse transpose of the completed row-frame matrix. |
| Section 4, pages 6–7 | Does the cut parametrization cover the entire finite auxiliary orbit, and does the boundary estimate exclude every degenerate limit? |
| Section 5, pages 7–8 | Is the transferred state an admissible competitor at the same M before any mode is removed? |
| Appendix B, page 10 | Does the parity change preserve the physical marginal and cut entropy? The fixed-parity matched-size corollary requires n≥1. |

The manuscript uses both total-parity components in its main fermionic definition. The empty physical system is included in that main statement; an odd-parity empty matched extension does not exist.

The numerical scripts test particular constructions and limiting cases. Local optimization values, equal padded candidate values, and agreement among AI reports are not proof steps.
