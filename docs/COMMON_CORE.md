# Shared mathematical core and its hypotheses

This note records dependencies shared by the [proof architectures](PROOF_ARCHITECTURES.md). The integration review reconstructed these interfaces and found no unresolved load-bearing defect in them. That is an internal mathematical assessment, not formal verification or human validation. Frozen source locators are recorded in [the evidence registry](../provenance/POST_STAGE_C.json).

## Physical subsystem and spectrum

For bosons, write `V=S D S^T` and set

$$
J=-S^{-T}\Omega S^T,\qquad g=\Omega J=SS^T,\qquad K=g^{-1}V.
$$

K is Hermitian in the g inner product, commutes with J, and satisfies `K>=I`. A J-invariant subspace is symplectic; its symplectic and g-orthogonal complements agree. The coordinate map `x -> S^T x` identifies its restricted covariance and commutator with a Hermitian compression of D and a canonical symplectic form. The eigenvalues of that compression, counted once per complex mode, are the **actual** reduced symplectic parameters. An arbitrary noncanonical frame requires both restricted forms, not its covariance matrix alone.

For fermions `Gamma=JK`, with orthogonal J, `0<=K<=I` and `[J,K]=0`. On a J-invariant retained subspace U, `Gamma_U=J_U K_U`; the K compression gives the actual reduced normal-mode parameters. The state restriction is to complete CAR modes with the graded permutation convention. Zero covariance modes permit an arbitrary compatible J on their even-dimensional kernel; no inverse of Gamma is required.

## Exact equality and global deletion

Hermitian interlacing and entropy monotonicity show nonincrease on the selected retained subspace. Bosons use the upper interlacing bound and increasing b; fermions use the lower bound and decreasing f. For discarded complex dimension q, **exact equality in this chain** forces

$$
\operatorname{Tr}K_D=q.
$$

The positive operator `K-I` (bosons) or `I-K` (fermions) has zero trace on D, so it annihilates D. This makes D pure and removes its cross block. Repeated eigenvalues do not require a unique eigenbasis. A pure marginal factors from every extension by positivity and rank-one support, so it is globally deletable, including with the graded fermionic convention.

The qualifier “selected” is essential. The false stronger claim is: *every complete-mode deletion preserving Gaussian entropy removes a pure factor*. Here are finite counterexamples, with modes ordered `(A,C_bad,C_pure)`, `Z=diag(1,-1)`, `epsilon=[[0,1],[-1,0]]`, and `X=[[0,1],[1,0]]`:

$$
V=\begin{pmatrix}3I_2&2\sqrt3 Z&0\\2\sqrt3 Z&5I_2&0\\0&0&I_2\end{pmatrix},
\qquad
\Gamma=\begin{pmatrix}\epsilon/2&X/\sqrt2&0\\-X/\sqrt2&0&0\\0&0&\epsilon\end{pmatrix}.
$$

V is a two-mode squeeze of `diag(I_2,3I_2)` with `cosh r=sqrt(3/2)`, followed by a vacuum factor. Its full parameters are `(1,3,1)`; retaining A and C_pure gives `(3,1)`, the same entropy. Yet C_bad has parameter 5 and is correlated with A. Gamma is an orthogonal congruence of `diag(epsilon,epsilon/2,epsilon)` using, on the first two modes, `Q=[[cI,tZ],[-tZ,cI]]`, `c=sqrt(2/3)`, `t=sqrt(1/3)`. Its full parameters are `(1,1/2,1)` and retained parameters `(1/2,1)`; C_bad is maximally mixed and correlated.

In both examples C_bad is not invariant under the adapted J. The actual constructions give `A+JA=A+C_bad` and `C intersect JC=C_pure`, so their equality clause selects the genuinely pure third mode. The examples challenge a dropped hypothesis, not the manuscript's lemma. They were supplied in Pro Stage C, Mathematical Reconstruction §9, and independently checked in the integration review.

Approximate equality also does not justify exact deletion. A recorded fermionic family has selected impurity delta but entropy gap `log(2)-f(delta)=delta^2/2+O(delta^4)`. This defeats a linear error bound; it does not rule out every possible quantitative argument. The present global proofs use exact attained optimizers before invoking exact rigidity.

## Admissibility and existence

- Auxiliary re-splitting uses complete orthogonal or symplectic frame completion inside the auxiliaries. It preserves the prescribed physical marginal.
- Finite canonical Gaussian purification and pure padding ensure nonempty comparison classes. Existence of a feasible matched purifier alone does not prove optimality.
- The manuscript's fixed-total attainment uses a fixed positive covariance lower bound and excludes degenerate physical cuts. Divergent frames at a fixed cut are local gauge changes and need not change entropy.
- Stage A and MR1 instead bound normalized auxiliary covariance entries. Stage A closes a marginal rank condition and repurifies; MR1 closes full polynomial purity. Both supply an actual optimizer before equality deletion.

The common dependency set is substantive even when no unresolved objection remains. Stage C attacks and the current reconstruction support these specific nodes; finite diagnostics, archive hashes and repeated model agreement do not replace their analytic arguments.
