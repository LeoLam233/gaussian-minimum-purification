> **Supplementary research record — not separately adversarially audited.**
> Frozen run: `MR1-1`; original outcome: `CLAIMED_PROOF`. Statements of proof below are the originating run's claims.
> Read the [review qualifications](../../REVIEW_NOTES.md) and [additional-results status](../../EXTRA_RESULTS.md). The original frozen text follows byte-for-byte after this notice.

---

# MR1 method-guided independent rederivation: Gaussian minimum purification

## Disclosure and result

This run is a **method-guided independent rederivation**. `INPUT/METHOD_FRAMEWORK.md` was supplied before the derivation and provided the proposed architecture (local one-mode compression, equality rigidity, fixed-size attainment, and global mode-count reduction). I therefore do **not** claim blind discovery of that architecture. Every research-level statement used from that framework is rederived below rather than accepted as a premise.

**Claimed result, pending external review:** for every finite-mode state in the bosonic and fermionic domains of `TASK.md`, the Gaussian entanglement of purification over arbitrary finite auxiliary mode numbers equals the minimum over matched auxiliary sizes, and this matched-size minimum is attained:

\[
E_P^{\mathrm G}(\rho_{AB})
=
\min_{\Psi\in\mathcal P_{n_A,n_B}(\rho_{AB})}
S(\rho^{\Psi}_{AA'}).
\]

The value and attainment statements are claimed for both bosons and fermions, including pure factors, repeated normal-mode parameters, all allowed boundary values, and empty subsystems. The proof does not address non-Gaussian purifications (Conjecture 1).

## Node status

| Node | Status | What is established here |
|---|---|---|
| G0 | **proved** | Conventions, fermionic reduction convention, explicit canonical Gaussian purifications, padding, and nonemptiness for every total auxiliary size `M>=n`; first moments handled for bosons. |
| F1 | **proved** | For `c>a`, a mode `P` can be selected using an auxiliary-only orthogonal Gaussian transformation such that `S(X C~) <= S(XC)`. The retained covariance is explicitly identified as the compression of the constructed Hermitian operator. |
| F2 | **proved** | For that selected mode, equality holds iff the mode is a pure decoupled factor. The proof uses interlacing, a trace identity, and `0<=K<=I`, not merely equality of entropies. |
| B1 | **proved** | Bosonic auxiliary-only symplectic mode selection and entropy compression. The selected plane is symplectic and the retained subsystem is the actual symplectic complement, not an abstract matrix compression. |
| B2 | **proved** | Equality for the selected bosonic compression forces `K=I` on the removed complex line, hence a pure covariance block and zero cross covariance; conversely a pure factor gives equality. |
| A_F | **proved** | Every nonempty fixed finite auxiliary-size/split fermionic feasible class is compact at the covariance level, and entropy is continuous. |
| A_B | **proved** | Every nonempty fixed finite auxiliary-size/split bosonic feasible class attains its infimum after auxiliary local Williamson normalization; bounded objective controls auxiliary marginal entropies and hence all covariance entries. |
| R | **proved** | Fixed-total minimizers can transfer an excess mode; equality rigidity makes the transferred mode globally deletable for `M>n`. This gives `e_M=e_{M-1}` for `M>n`, a matched minimizer at `M=n`, and a direct padding/transfer comparison for `M<n`. |

No node is left conditional in this run.

---

## 1. Inputs, imported standard facts, and conventions

Write
\[
n=n_A+n_B.
\]
For bosons I use the packet convention
\[
[\hat r_j,\hat r_k]=i\Omega_{jk},\qquad
V_{jk}=\operatorname{Tr}\rho\{\hat r_j-d_j,\hat r_k-d_k\},
\]
so the vacuum covariance is `I`, physical symplectic eigenvalues satisfy `nu_j>=1`, and a pure covariance obeys
\[
V\Omega V=\Omega.
\]
For fermions I use Hermitian Majoranas with `{c_j,c_k}=2 delta_jk` and covariance
\[
\Gamma_{jk}=\frac i2\operatorname{Tr}\rho[c_j,c_k],
\]
with one-mode parameters `0<=lambda_j<=1` and purity `Gamma^2=-I`.

The following are treated as standard Gaussian/linear-algebra facts, not as research lemmas from the supplied framework:

1. Williamson normal form for a positive bosonic covariance and real skew normal form for a fermionic covariance.
2. Finite Gaussian states are determined by their first and second moments (bosons) or by the parity-even quasifree covariance (fermions), and a complete-mode subsystem is obtained by restricting those moments to the corresponding canonical subspace.
3. The entropy formulas from `CONVENTIONS.md`:
   \[
   b(\nu)=\frac{\nu+1}{2}\log\frac{\nu+1}{2}
   -\frac{\nu-1}{2}\log\frac{\nu-1}{2},
   \]
   \[
   f(\lambda)=-\frac{1+\lambda}{2}\log\frac{1+\lambda}{2}
   -\frac{1-\lambda}{2}\log\frac{1-\lambda}{2}.
   \]
4. Cauchy interlacing for a Hermitian operator compressed to a complex codimension-one subspace.
5. Standard von Neumann entropy inequalities, in particular Araki--Lieb.

Exact source locators used for background and provenance are listed in section 11. In particular, WJEH2021, Sec. 6.1, PDF p. 43 is used only to identify Conjecture 2; its later informal discussion is not taken as proof.

### Fermionic ordering and reduction

I fix the complete-mode order
\[
A,\ B,\ A',\ B'.
\]
For a different cut I reorder **whole modes**, with the standard fermionic swap/Jordan--Wigner convention, before taking the ordinary Hilbert-space partial trace. All density operators in the task are parity invariant; a pure parity-invariant state has definite total parity. In covariance language the reduced quasifree state is therefore the principal restriction to the corresponding complete-mode Majorana subspace. Product statements below are understood in this complete-mode convention. No coherent superposition of total parities is introduced.

---

## 2. G0: explicit nonemptiness, padding, and local operations

### 2.1 Bosonic canonical purification

Let the fixed physical covariance on `AB` be
\[
V_{AB}=SDS^T,\qquad
D=\bigoplus_{j=1}^{n}\nu_j I_2,\quad \nu_j\ge1,
\]
with `S` symplectic. Put
\[
J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\]
and, for each physical mode, set `s_j=sqrt(nu_j^2-1)`. In the ordering physical-normal-modes followed by one auxiliary mode for each physical mode, define
\[
W=
\begin{pmatrix}
D&C\\ C&D
\end{pmatrix},\qquad
C=\bigoplus_j s_j Z.
\]
Since `Z J_2 Z=-J_2` and `ZJ_2+J_2Z=0`, each two-mode block satisfies
\[
W_j(J_2\oplus J_2)W_j=J_2\oplus J_2,
\]
hence `W` is a pure covariance. Then
\[
V_{\rm pur}=(S\oplus I)W(S^T\oplus I)
\]
is pure and has physical block `V_AB`. Give the physical modes their prescribed first moment `d_AB` and take the auxiliary first moments to be zero; a physical Weyl displacement realizes this without changing the covariance or purity.

Thus `n` auxiliary modes always suffice. Extra auxiliary modes can be added in independent vacuum states. Since the auxiliary modes can be labelled as `A'` or `B'` arbitrarily, for every `M>=n` and every split `k+(M-k)` the feasible class is nonempty.

### 2.2 Fermionic canonical purification

Bring the physical covariance to real skew normal form
\[
\Gamma_{AB}=Q A Q^T,\qquad
A=\bigoplus_{j=1}^n \lambda_j J_2,
\quad 0\le\lambda_j\le1.
\]
Let
\[
R=\bigoplus_{j=1}^n \sqrt{1-\lambda_j^2}\,I_2.
\]
Then
\[
\Gamma_0=
\begin{pmatrix}
A&R\\-R&-A
\end{pmatrix}
\]
is real antisymmetric and obeys `Gamma_0^2=-I`: the diagonal blocks give
`A^2-R^2=-I`, while the off-diagonal blocks vanish because each block of `A` commutes with the corresponding scalar block of `R`. Hence
\[
\Gamma_{\rm pur}=(Q\oplus I)\Gamma_0(Q^T\oplus I)
\]
is a pure Gaussian covariance with physical block `Gamma_AB`. It represents a definite-parity pure quasifree state, hence lies in the primary domain. Extra independent pure fermionic modes give padding to every `M>=n`, and again the auxiliary labels may be split arbitrarily between `A'` and `B'`.

### 2.3 Local changes used later

For bosons, a symplectic change inside an auxiliary subsystem is implemented (up to phase) by a Gaussian unitary on that subsystem. For fermions, below I choose an **orientation-preserving** orthogonal basis change inside the auxiliary Majorana space, so it lies in `SO(2c)` and is implemented by a parity-preserving quadratic Gaussian unitary. Such local unitaries preserve the fixed physical marginal and the entropy of a cut containing the whole transformed auxiliary side.

This completes G0.

---

## 3. A common geometric selection lemma

Let `E=X\oplus C` be the real coefficient space of a Gaussian state `rho_XC`, with `dim_R X=2a`, `dim_R C=2c`, and `c>a`. Suppose `J:E->E` is a real complex structure (`J^2=-I`). Define
\[
L=C\cap JC.
\]
Since both `C` and `JC` have dimension `2c` inside a `2(a+c)`-dimensional space,
\[
\dim_R L\ge 2c+2c-2(a+c)=2(c-a)>0.
\]
Moreover `L` is `J`-invariant: if `v\in L`, then `v\in C` and `v=Jw` for some `w\in C`; hence `Jv=-w\in C`, and because `v\in C`, also `Jv\in JC`.

Therefore `L` contains a real two-plane
\[
P=\operatorname{span}_R\{v,Jv\}
\]
which is a single complex line for `J`. What remains is to construct, separately for fermions and bosons, a `J` adapted to the state for which `P` is a genuine physical mode and for which the actual retained subsystem is a Hermitian compression.

---

## 4. F1 and F2: fermionic local compression and equality rigidity

Let `rho_XC` be a parity-invariant fermionic Gaussian state with `a` modes in `X` and `c>a` modes in `C`. Put `d=a+c`.

### 4.1 Construction of `J` and `K` without inverting `Gamma`

Take a real skew normal form
\[
\Gamma=Q\left(\bigoplus_{j=1}^d \lambda_jJ_2\right)Q^T,
\qquad 0\le\lambda_j\le1.
\]
Define
\[
J=Q\left(\bigoplus_{j=1}^d J_2\right)Q^T,
\qquad
K=Q\left(\bigoplus_{j=1}^d \lambda_j I_2\right)Q^T.
\]
Then
\[
J^2=-I,\qquad J^T=-J,\qquad J^TJ=I,
\]
\[
0\le K\le I,\qquad [J,K]=0,\qquad \Gamma=JK,
\]
and no inverse of `Gamma` has been used. With `J` regarded as multiplication by `i`, the real Euclidean space becomes a complex Hilbert space of complex dimension `d`; `K` is a positive Hermitian complex-linear operator whose complex eigenvalues are precisely the mode parameters `lambda_1,...,lambda_d`, each counted once.

### 4.2 The selected physical mode and the actual retained subsystem

Apply the common selection lemma to the auxiliary Majorana subspace `C`. Choose nonzero `v\in C\cap JC` and let
\[
P=\operatorname{span}_R\{v,Jv\}\subset C.
\]
Because `J` is orthogonal and skew,
\[
\langle v,Jv\rangle=0,
\]
so after normalization `(v,Jv)` is an orthonormal Majorana pair: `P` is a complete fermionic mode.

Let
\[
\widetilde C=C\cap P^\perp,
\qquad
Y=X\oplus\widetilde C=P^\perp.
\]
Since `P` is `J`-invariant and `J` is orthogonal, `Y` is also `J`-invariant. Choose an oriented orthonormal basis of `C` adapted to `C=\widetilde C\oplus P`; this can be chosen in `SO(2c)`, hence realized by a local parity-preserving Gaussian transformation on `C` alone.

Let `Pi_Y` be the Euclidean orthogonal projection. Because `Pi_Y` commutes with `J`, the covariance of the **actual retained subsystem** `Y` is
\[
\Gamma_Y=\Pi_Y\Gamma|_Y
=J_YK_Y,
\qquad
K_Y:=\Pi_YK|_Y.
\]
Thus the retained one-mode parameters are exactly the complex eigenvalues of the Hermitian compression `K_Y`.

### 4.3 Entropy inequality (F1)

Order the eigenvalues of `K` as
\[
0\le\lambda_1\le\cdots\le\lambda_d\le1
\]
and those of `K_Y` as
\[
0\le\mu_1\le\cdots\le\mu_{d-1}\le1.
\]
Cauchy interlacing gives
\[
\lambda_j\le\mu_j\le\lambda_{j+1},\qquad j=1,\ldots,d-1.
\]
The fermionic one-mode entropy `f` is continuous and strictly decreasing on `[0,1]`, with `f(1)=0`; indeed for `0<lambda<1`,
\[
f'(\lambda)=\frac12\log\frac{1-\lambda}{1+\lambda}<0.
\]
Using the **lower** side of interlacing,
\[
f(\mu_j)\le f(\lambda_j).
\]
Therefore
\[
S(Y)=\sum_{j=1}^{d-1}f(\mu_j)
\le \sum_{j=1}^{d-1}f(\lambda_j)
\le \sum_{j=1}^{d}f(\lambda_j)=S(XC).
\]
This proves F1.

### 4.4 Equality condition (F2), proved separately

The entropy difference has the decomposition
\[
S(XC)-S(Y)
=f(\lambda_d)+\sum_{j=1}^{d-1}\bigl[f(\lambda_j)-f(\mu_j)\bigr],
\]
and every term is nonnegative. Hence equality implies
\[
\lambda_d=1,\qquad \mu_j=\lambda_j\quad(j=1,\ldots,d-1).
\]
Taking the complex trace,
\[
\operatorname{Tr}_{\mathbb C}K-
\operatorname{Tr}_{\mathbb C}K_Y=1.
\]
If `p` is a unit complex vector spanning the removed complex line `P`, compression gives
\[
\operatorname{Tr}_{\mathbb C}K-
\operatorname{Tr}_{\mathbb C}K_Y
=\langle p,Kp\rangle.
\]
Thus `\langle p,Kp\rangle=1`. Since `I-K\succeq0`,
\[
\langle p,(I-K)p\rangle=0
\quad\Longrightarrow\quad
(I-K)p=0.
\]
Because `K` is complex linear, `K=I` on the real plane `P`; because `K` is self-adjoint, both `P` and `Y` reduce `K`. Since `J` also preserves both, `Gamma=JK` is block diagonal for `Y\oplus P`, and on `P` one has
\[
\Gamma_P=J_P,\qquad \Gamma_P^2=-I.
\]
So `P` is a pure one-mode Gaussian state and there are no cross covariances.

Both reduced states are parity-invariant Gaussian states. Their product has the same block-diagonal covariance as `rho_XC`; uniqueness of a parity-invariant quasifree state from its covariance gives
\[
\rho_{XC}=\rho_Y\otimes |\chi\rangle\langle\chi|_P.
\]
Conversely, if this factorization holds with `P` pure, entropy additivity gives `S(Y)=S(XC)`. Thus for the selected mode
\[
S(Y)=S(XC)
\iff
\rho_{XC}=\rho_Y\otimes |\chi\rangle\langle\chi|_P.
\]
This proves F2, including the boundary cases `lambda=0,1` and repeated parameters; no generic-spectrum assumption was used.

---

## 5. B1 and B2: bosonic local compression and equality rigidity

Let `rho_XC` be a finite-covariance bosonic Gaussian state with `a` modes in `X` and `c>a` in `C`, and let `V` be its centered covariance. Put `d=a+c`.

### 5.1 Constructing a compatible complex structure on coefficient vectors

Take a Williamson decomposition
\[
V=SDS^T,
\qquad
D=\bigoplus_{j=1}^{d}\nu_jI_2,
\quad \nu_j\ge1,
\]
with `S Omega S^T=Omega`. Let
\[
J_0=-\Omega,
\qquad
J=S^{-T}J_0S^T.
\]
This is the required map on **observable coefficient vectors**. Direct calculation gives
\[
J^2=-I,
\qquad
J^T\Omega J=\Omega.
\]
Moreover
\[
g:=\Omega J
=\Omega S^{-T}(-\Omega)S^T
=S(\Omega(-\Omega))S^T
=SS^T>0,
\]
where `Omega S^{-T}=S Omega` was used. Finally,
\[
J^TVJ=V,
\]
because `J_0` commutes with the block-scalar `D` and is orthogonal.

Define
\[
K=g^{-1}V=S^{-T}DS^T.
\]
Then
\[
[K,J]=0,
\qquad
gK=K^Tg=V,
\]
and, with respect to the positive inner product `g`, `K` is self-adjoint and positive. As a complex-linear Hermitian operator for the complex structure `J`, its complex eigenvalues are exactly the symplectic eigenvalues `nu_j`, counted once, and
\[
K\ge I.
\]

### 5.2 The selected plane is a physical bosonic mode

Apply the common selection lemma to `C` and choose `v\in C\cap JC`, `v\neq0`. Let
\[
P=\operatorname{span}_R\{v,Jv\}\subset C.
\]
Because `g=Omega J` is positive,
\[
\Omega(v,Jv)=g(v,v)>0.
\]
Thus `P` is a nondegenerate symplectic two-plane, i.e. a genuine single bosonic mode after rescaling `v` so that `Omega(v,Jv)=1`.

Let
\[
\widetilde C=C\cap P^{\Omega},
\]
where `P^{Omega}` is the symplectic complement in the full coefficient space. Since `P` is symplectic,
\[
C=\widetilde C\oplus^{\Omega}P,
\]
and a symplectic basis of `C` adapted to this direct sum is obtained by a transformation in `Sp(2c,R)` acting on `C` alone. Hence the split is physically realizable by a local Gaussian unitary.

Set
\[
Y=X\oplus\widetilde C=P^{\Omega}.
\]
This is the **actual retained subsystem** after the selected physical mode is removed. Because `P` is `J`-invariant and `J` is symplectic, `Y` is `J`-invariant: if `y\in Y` and `p\in P`, write `p=Jq` with `q\in P`; then
\[
\Omega(Jy,p)=\Omega(Jy,Jq)=\Omega(y,q)=0.
\]
Furthermore
\[
P^{\Omega}=P^{\perp_g},
\]
because `g(y,p)=Omega(y,Jp)` and `JP=P`.

### 5.3 Identification of the retained symplectic spectrum

Let `Pi_Y` be the `g`-orthogonal projection onto `Y`. Because `Y` and `P` are both `J`-invariant, `Pi_Y` commutes with `J`. Define the Hermitian compression
\[
K_Y=\Pi_YK|_Y.
\]
For `u,v in Y`, the restricted covariance is
\[
V_Y(u,v)=V(u,v)=g(u,Kv)=g(u,K_Yv).
\]
Also `g_Y=Omega_YJ_Y`. Choose a complex `g`-orthonormal eigenbasis of `K_Y`. For one normalized eigenvector `e` with eigenvalue `mu`, the real pair `(e,Je)` satisfies
\[
\Omega(e,Je)=1,
\]
and the restricted covariance on that pair is `mu I_2`. Hence the complex eigenvalues of `K_Y` are exactly the symplectic eigenvalues of the **physical retained covariance** `V_Y`.

This is the step that prevents an abstract interlacing argument from being applied to a matrix unrelated to the retained subsystem.

### 5.4 Entropy inequality (B1)

Order the full symplectic eigenvalues and retained ones as
\[
1\le\nu_1\le\cdots\le\nu_d,
\qquad
1\le\mu_1\le\cdots\le\mu_{d-1}.
\]
Cauchy interlacing for the complex Hermitian compression gives
\[
\nu_j\le\mu_j\le\nu_{j+1}.
\]
The bosonic one-mode entropy `b` is continuous and strictly increasing on `[1,\infty)`, with `b(1)=0`; for `nu>1`,
\[
b'(\nu)=\frac12\log\frac{\nu+1}{\nu-1}>0.
\]
Here the needed side of interlacing is the **upper** one:
\[
b(\mu_j)\le b(\nu_{j+1}).
\]
Therefore
\[
S(Y)=\sum_{j=1}^{d-1}b(\mu_j)
\le\sum_{j=2}^{d}b(\nu_j)
\le\sum_{j=1}^{d}b(\nu_j)=S(XC).
\]
This proves B1.

### 5.5 Equality condition (B2), proved separately

The entropy difference is
\[
S(XC)-S(Y)
=b(\nu_1)+\sum_{j=1}^{d-1}\bigl[b(\nu_{j+1})-b(\mu_j)\bigr],
\]
again a sum of nonnegative terms. Equality therefore implies
\[
\nu_1=1,
\qquad
\mu_j=\nu_{j+1}\quad(j=1,\ldots,d-1).
\]
Taking the complex trace gives
\[
\operatorname{Tr}_{\mathbb C}K-
\operatorname{Tr}_{\mathbb C}K_Y=1.
\]
If `p` is a unit complex vector spanning `P`, this difference is
\[
\langle p,Kp\rangle_g=1.
\]
Since `K-I\succeq0` as a Hermitian operator,
\[
\langle p,(K-I)p\rangle_g=0
\quad\Longrightarrow\quad
(K-I)p=0.
\]
Thus `K=I` on `P`; self-adjointness makes `P` and `Y` reducing subspaces of `K`. They are already `g`-orthogonal and `J`-invariant, so
\[
V=gK
\]
has zero cross block between `Y` and `P`, while on `P` one has `V_P=g_P`. In the normalized canonical basis `(p,Jp)`,
\[
\Omega_P=J_2,
\qquad
V_P=I_2,
\]
so the selected mode is pure.

Bosonic first moments cause no obstruction: the displacement vector simply splits as `(d_Y,d_P)`. The product Gaussian state `rho_Y \otimes |chi><chi|_P` has exactly the same first moments and block-diagonal covariance as `rho_XC`, hence Gaussian uniqueness gives
\[
\rho_{XC}=\rho_Y\otimes|\chi\rangle\langle\chi|_P.
\]
Conversely a pure product factor contributes zero entropy, so equality holds. Hence
\[
S(Y)=S(XC)
\iff
\rho_{XC}=\rho_Y\otimes|\chi\rangle\langle\chi|_P.
\]
This proves B2, including `nu=1` pure factors and repeated Williamson eigenvalues.

---

## 6. A_F: fixed finite-size attainment for fermions

Fix finite auxiliary sizes `(m_A,m_B)` and suppose the feasible class is nonempty. Let the total number of modes in the pure extension be `N=n+m_A+m_B`.

At covariance level, a pure fermionic Gaussian extension is a real antisymmetric matrix `Gamma` satisfying
\[
\Gamma^2=-I
\]
and with the prescribed physical `AB` principal block. From antisymmetry and purity,
\[
\Gamma^T\Gamma=(-\Gamma)\Gamma=I,
\]
so every entry is bounded. The conditions

- `Gamma^T=-Gamma`,
- `Gamma^2=-I`,
- fixed physical principal block,

are closed polynomial/linear conditions. Therefore the feasible covariance set is a closed subset of a bounded finite-dimensional set, hence compact. It includes both pure-state parity components that are actually compatible with the fixed marginal; taking their union does not spoil compactness.

The reduced covariance on `AA'` depends continuously on `Gamma`, its singular/mode parameters depend continuously on the matrix, and `f` is continuous on `[0,1]`. Hence `S(AA')` is continuous on the compact feasible set and attains its minimum.

A finite union over the possible splits at fixed total `M` therefore also attains the fixed-total minimum whenever the total class is nonempty. This proves A_F.

---

## 7. A_B: fixed finite-size attainment for bosons

Fix finite auxiliary sizes `(m_A,m_B)` and a nonempty bosonic feasible class. The issue is noncompactness of the symplectic group; I do not assume compactness of pure covariances.

Let
\[
I=\inf S(AA')
\]
over this fixed split and choose a minimizing sequence of pure Gaussian extensions. Since the class is nonempty and every finite covariance has finite Gaussian entropy, `I<\infty`. Discard finitely many terms so that
\[
S(AA')\le C
\]
for one finite constant `C` along the sequence.

### 7.1 Normalize auxiliary first moments and marginal covariances

Auxiliary Weyl displacements on `A'` and `B'` set their first moments to zero without changing the physical first moments, purity, or the cut entropy.

Next apply, independently on `A'` and `B'`, local Williamson transformations. These are local Gaussian unitaries, so they preserve feasibility and `S(AA')`. After this normalization,
\[
V_{A'}=\bigoplus_i \alpha_i I_2,
\qquad
V_{B'}=\bigoplus_j \beta_j I_2.
\]

### 7.2 Bounded objective bounds the auxiliary Williamson eigenvalues

The physical marginal is fixed, so `S(A)` and `S(B)` are fixed finite numbers. Araki--Lieb gives
\[
S(A')\le S(AA')+S(A)\le C+S(A).
\]
Because the full extension is pure, `S(BB')=S(AA')`, and similarly
\[
S(B')\le S(BB')+S(B)\le C+S(B).
\]
But
\[
S(A')=\sum_i b(\alpha_i),
\qquad
S(B')=\sum_j b(\beta_j).
\]
The function `b` is increasing and unbounded as `nu\to\infty`. Therefore every `alpha_i` and `beta_j` is bounded above by a finite constant depending only on `C`, the fixed physical marginal, and the finite auxiliary sizes.

Consequently all diagonal entries of the normalized auxiliary blocks are uniformly bounded.

### 7.3 All covariance entries are bounded

Every bosonic covariance matrix `V` is positive definite. For any two real coordinates `r,s`, positivity of the `2\times2` principal minor gives
\[
|V_{rs}|^2\le V_{rr}V_{ss}.
\]
The physical diagonal entries are fixed, and the normalized auxiliary diagonal entries have just been uniformly bounded. Hence **every entry** of the total covariance matrix is uniformly bounded along the normalized minimizing sequence.

### 7.4 Passage to the limit

Finite dimensionality now gives a convergent subsequence
\[
V_j\longrightarrow V_*.
\]
The physical `AB` block remains the prescribed one. The physical inequality `V_j+i\Omega\succeq0` is closed, so it survives. Purity is the polynomial identity
\[
V_j\Omega V_j=\Omega,
\]
therefore
\[
V_*\Omega V_*=\Omega.
\]
This identity makes `V_*` invertible; combined with the closed positive-semidefinite limit it is positive definite. Thus `V_*` is a finite, normal, pure bosonic Gaussian covariance, not an infinite-squeezing boundary object. The first moments also converge (indeed the physical ones are fixed and the auxiliary ones were normalized to zero).

The reduced covariance on `AA'` converges entrywise. Its symplectic eigenvalues depend continuously on the matrix (including repeated eigenvalues), and `b` is continuous on `[1,\infty)`. Hence
\[
S_{V_j}(AA')\longrightarrow S_{V_*}(AA').
\]
Therefore `V_*` attains the infimum for the fixed split. A finite number of splits at a fixed total `M` gives attainment for the fixed-total optimization.

This proves A_B and explicitly excludes the noncompact escape that would invalidate a naive compactness argument.

---

## 8. R: global reduction to the matched split

For `M>=n`, define
\[
e_M=\min_{0\le k\le M}\ 
\min_{\Psi\in\mathcal P_{k,M-k}(\rho_{AB})}
S(AA').
\]
G0 gives nonemptiness for every split, and A_F/A_B justify writing `min` rather than `inf`.

### 8.1 One excess mode can be transferred at no cost in a fixed-total minimizer

Take a minimizer for `e_M` with split `(k,M-k)`. If `M>n`, then at least one auxiliary side is oversized relative to its physical side.

Suppose first that
\[
k>n_A.
\]
Apply F1/F2 or B1/B2 to the reduced Gaussian state on `AA'`, with `X=A` and `C=A'`. After a Gaussian transformation on `A'` alone, write
\[
A'=\widetilde A'\oplus P,
\]
where `P` is one complete mode and
\[
S(A\widetilde A')\le S(AA')=e_M.
\]
Keep the same global pure state but **reassign** the selected auxiliary mode `P` from `A'` to `B'`. This is an admissible competitor at the same total `M`, now with split `(k-1,M-k+1)`, and its cut entropy is `S(A\widetilde A')`. By minimality of `e_M`,
\[
e_M\le S(A\widetilde A')\le e_M.
\]
Hence equality holds.

If instead `M-k>n_B`, apply the same argument to the reduced state on `BB'`. Since the global state is pure,
\[
S(BB')=S(AA')=e_M.
\]
After removing one selected mode from `B'` and reassigning it to `A'`, the new cut entropy equals `S(B\widetilde B')\le e_M`, and fixed-total minimality again forces equality.

Thus an excess mode can always be transferred without changing the optimum.

### 8.2 Equality makes the selected mode globally deletable when `M>n`

Continue with the first case. Equality in the selected local compression invokes F2/B2, so
\[
\rho_{AA'}=
\rho_{A\widetilde A'}\otimes |\chi\rangle\langle\chi|_P.
\]
In particular the marginal on `P` is pure. A subsystem with a pure marginal factorizes from any global state; for the present global pure state,
\[
|\Psi\rangle_{ABA'B'}
=|\chi\rangle_P\otimes|\Phi\rangle_{AB\widetilde A'B'}.
\]
In the fermionic case this is read in the complete-mode tensor convention fixed above. The remaining state `|Phi>` is again pure Gaussian (it is a Gaussian reduction and is pure), has the same prescribed physical marginal, and has one fewer auxiliary mode. Deleting `P` leaves the cut entropy equal to `e_M`. Therefore
\[
e_{M-1}\le e_M.
\]

Conversely, padding any `(M-1)`-auxiliary pure Gaussian extension by an independent pure mode gives an `M`-auxiliary extension with the same cut entropy, so
\[
e_M\le e_{M-1}.
\]
Hence for every `M>n`,
\[
\boxed{e_M=e_{M-1}}.
\]
Iterating,
\[
e_M=e_n\qquad(M\ge n).
\]
The argument is identical if the excess side was `B'`.

### 8.3 At total `n`, transfers reach exactly `(n_A,n_B)`

Take a minimizer for `e_n` with split `(k,n-k)`. If `k=n_A`, it is already matched. If `k>n_A`, `A'` is oversized and the transfer step above produces another fixed-total minimizer with split `(k-1,n-k+1)`. If `k<n_A`, then
\[
n-k>n-n_A=n_B,
\]
so `B'` is oversized and one transfers a mode in the opposite direction. Repeating finitely many times reaches the exact split
\[
(n_A,n_B)
\]
while preserving the value `e_n` at every step.

Therefore
\[
e_n=
\min_{\Psi\in\mathcal P_{n_A,n_B}(\rho_{AB})}
S(AA'),
\]
and the right-hand side is attained.

### 8.4 Auxiliary totals below `n`

Let an arbitrary admissible pure Gaussian extension have total auxiliary count
\[
M<n
\]
and cut entropy `E`. Pad it by `n-M` independent pure auxiliary modes, assigned arbitrarily to either auxiliary side. The total becomes `n` and the cut entropy remains exactly `E`.

At total `n`, if the split is not `(n_A,n_B)`, exactly one side is oversized. Apply the local compression and transfer step to that side. This does **not** require the state to be a fixed-total minimizer: it only uses the inequality, so the entropy does not increase. Repeat until the split is matched. We have constructed a matched-size pure Gaussian extension with entropy at most `E`. Hence every admissible extension with `M<n` obeys
\[
E\ge
\min_{\Psi\in\mathcal P_{n_A,n_B}(\rho_{AB})}S(AA').
\]

### 8.5 Global comparison

Let
\[
m_*:=
\min_{\Psi\in\mathcal P_{n_A,n_B}(\rho_{AB})}S(AA')=e_n.
\]
For `M>=n`, every extension has entropy at least `e_M=e_n=m_*`. For `M<n`, section 8.4 gives the same lower bound. Therefore the infimum over **all** finite auxiliary sizes is at least `m_*`. The matched class itself is part of the unrestricted optimization, so the reverse inequality is immediate. Consequently
\[
\boxed{
E_P^{\mathrm G}(\rho_{AB})=m_*
}.
\]
Because `m_*` is attained in the matched class, the unrestricted infimum is attained there as well.

This proves R.

---

## 9. Boundary and domain checks

1. **Pure physical factors / pure normal modes.** Fermionic `lambda=1` and bosonic `nu=1` were retained throughout. The entropy functions are continuous at these endpoints and equality rigidity explicitly lands at those pure values.
2. **Fermionic zero modes.** `lambda=0` is allowed. The construction `Gamma=JK` never inverts `Gamma`, so zero modes are harmless.
3. **Repeated normal-mode parameters.** Only Hermitian interlacing and traces are used; no simple-spectrum eigenvector choice is required.
4. **Bosonic first moments.** Entropy depends only on covariance. Physical first moments are kept fixed; auxiliary displacements are local normalization freedoms in A_B. In B2 the final product statement includes the split displacement vector.
5. **Normality / no infinite squeezing.** A_B obtains a bounded covariance subsequence and a finite positive-definite pure limit. Singular infinite-squeezing limits are never admitted as states.
6. **Empty `A` or `B`.** The local lemmas allow `a=0`. The global transfer argument remains valid. In particular if, say, `A` is empty, the matched split has `A'` empty and gives zero cut entropy as expected.
7. **Completely empty system `n=0`.** The matched extension has no auxiliary modes and entropy zero. This directly establishes the theorem. The reduction argument is also consistent with it.
8. **Fermionic parity.** The primary optimization allows either definite total parity. The compactness proof includes both covariance components compatible with the marginal. Local basis changes can be chosen in `SO`, so no coherent parity superposition is introduced. A deleted pure mode has definite parity, and the remaining factor therefore also has definite parity.

---

## 10. Final scope statement

### Bosons

- **Value:** proved in this run, conditional only on the standard finite-dimensional Gaussian background listed in section 1. Arbitrary finite auxiliary sizes cannot lower the value below the matched split `(n_A,n_B)`.
- **Attainment:** proved. The matched-size class is nonempty and its entropy minimum is attained by a normal finite-covariance pure Gaussian extension.

### Fermions

- **Value:** proved in this run for parity-invariant quasifree mixed states with the primary optimization allowing pure Gaussian extensions of either definite total parity.
- **Attainment:** proved. The matched-size class is compact at covariance level and contains a minimizer.

The run outcome is therefore **CLAIMED_PROOF** under the output-contract terminology; that label records a completed derivation awaiting review, not an externally certified theorem.

---

## 11. Exact source premises and locators

The derivation above is new to this run; the following supplied sources were used only for problem provenance and standard Gaussian background.

1. **WJEH2021** — B. Windt, A. Jahn, J. Eisert, L. Hackl, *Local optimization on pure Gaussian state manifolds*, SciPost Phys. 10, 066 (2021), published PDF included in the packet.
   - **PDF p. 43, Sec. 6.1:** exact statement of Conjecture 2 (minimum purification conjecture), and separation from Conjecture 1.
   - **PDF pp. 16--19, Sec. 2.6:** standard discussion of Gaussian purification and normal forms. I did not use its sufficiency claims as a substitute for the explicit canonical purifications in G0.
   - **PDF pp. 39--41, Sec. 5.2:** Gaussian EoP setup and entropy objective.
   - While consulting the permitted source discussion, I also encountered the informal auxiliary-mode statement on **PDF p. 46, Sec. 6.3**. It was not used as a theorem or as a proof premise.

2. **HB2021** — L. Hackl, E. Bianchi, *Bosonic and fermionic Gaussian states from Kähler structures*, SciPost Phys. Core 4, 025 (2021), published PDF included in the packet.
   - **PDF pp. 46--48, Secs. 4.1.2 and Proposition 13:** canonical subsystem decompositions and Gaussian reduction to a subsystem.
   - **PDF pp. 48--49, Sec. 4.1.3:** Gaussian entanglement/von Neumann entropy formulas and endpoint ranges.
   - **PDF p. 45, Table 4:** covariance/complex-structure summary used only as background cross-check.

3. **Packet convention sheet** `INPUT/CONVENTIONS.md`: covariance normalizations, entropy functions, physical ranges, and pure covariance criteria used throughout.

No internet source, connector, prior conversation, saved memory, unrelated local research file, external mathematical code, or other agent was used.

---

## 12. Strongest remaining review target

No mathematical node is intentionally left unresolved. The two places most worth hostile rechecking are precisely the places the supplied framework warned about:

1. **Bosonic physical compression:** section 5.3 identifies the covariance of the actual retained subsystem `Y=P^\Omega` with the `g`-Hermitian compression `K_Y`; this uses both `P^\Omega=P^{\perp_g}` and `J`-invariance. The symplectic eigenvalues are then obtained in a `g`-orthonormal `J`-paired eigenbasis, so the interlacing is applied to the correct physical covariance.
2. **Bosonic attainment:** section 7 does not compactify the symplectic group. It normalizes each auxiliary marginal locally, uses Araki--Lieb plus bounded objective to bound its Williamson eigenvalues, then uses positivity to bound every cross-covariance entry. Purity survives the finite matrix limit and prevents a singular covariance.

Those checks remove the strongest objections identified in the supplied method framework. The result remains, as required by the contract, a claimed proof pending independent mathematical review.
