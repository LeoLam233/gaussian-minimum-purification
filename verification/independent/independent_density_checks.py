"""Cold-audit checks; no imports from the manuscript verification package.

Bosons: recover J from a raw covariance, implement an auxiliary-only canonical
frame, integrate the full coordinate density kernel, and diagonalize the retained
integral kernel by converged Gauss-Hermite Nystrom quadrature. The before entropy
comes from the generating thermal probabilities, not a symplectic eigensolver.
Fermions: construct density matrices with exact pure/zero/repeated occupancies,
act by elementary Clifford rotations, reconstruct covariance by Fock traces,
implement the selected SO frame by Givens rotations, and trace the density matrix.
Also exercise signed (graded) permutations and parity-changing auxiliary Majoranas.
All floating point tests are diagnostics, not rigorous error enclosures or proofs.
"""
from __future__ import annotations
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import itertools
import json
from pathlib import Path
import platform
import sys

import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.linalg import block_diag, expm, null_space, sqrtm
from scipy.special import xlogy

ROOT = Path(__file__).resolve().parent
SEED = 202609240731
J2 = np.array([[0., 1.], [-1., 0.]])


def om(n):
    return np.kron(np.eye(n), J2)


def ent(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2)
    assert w.min() > -2e-10, w.min()
    assert abs(w.sum() - 1) < 2e-9, w.sum()
    w = np.maximum(w, 0)
    return float(-xlogy(w, w).sum())


def product(items):
    r = np.ones((1, 1), complex)
    for a in items:
        r = np.kron(r, a)
    return r


def boson_kernel_data(v):
    n = len(v) // 2
    pos, mom = np.arange(0, 2*n, 2), np.arange(1, 2*n, 2)
    x, z, y = v[np.ix_(pos, pos)], v[np.ix_(pos, mom)], v[np.ix_(mom, mom)]
    a = np.linalg.inv(x)
    c, m = y - z.T @ a @ z, a @ z
    norm = np.pi**(-n/2) / np.sqrt(np.linalg.det(x))
    return x, a, c, m, norm


def kernel(v, q, qp):
    _, a, c, m, norm = boson_kernel_data(v)
    u, delta = (q+qp)/2, q-qp
    return norm * np.exp(-u@a@u - delta@c@delta/4 + 1j*u@m@delta)


def trace_last_kernel(v, q, qp):
    # Analytic Gaussian integral over the same last coordinate on bra and ket.
    _, a, c, m, norm = boson_kernel_data(v)
    u, delta = (q+qp)/2, q-qp
    lin = -2*a[-1, :-1]@u + 1j*m[-1, :-1]@delta
    exponent = (-u@a[:-1, :-1]@u - delta@c[:-1, :-1]@delta/4
                + 1j*u@m[:-1, :-1]@delta + lin*lin/(4*a[-1, -1]))
    return norm*np.sqrt(np.pi/a[-1, -1])*np.exp(exponent)


def kernel_entropy(v, order):
    x, a, c, m, norm = boson_kernel_data(v)
    n = len(x)
    nodes, weights = hermgauss(order)
    tuples = np.array(list(itertools.product(range(order), repeat=n)))
    grid = nodes[tuples]
    integ_weights = np.prod(weights[tuples], axis=1)*np.exp((grid*grid).sum(axis=1))
    chol = np.linalg.cholesky(x)
    qs = grid @ chol.T
    u = (qs[:, None, :] + qs[None, :, :])/2
    delta = qs[:, None, :] - qs[None, :, :]
    exponent = (-np.einsum('...i,ij,...j->...', u, a, u)
                - np.einsum('...i,ij,...j->...', delta, c, delta)/4
                + 1j*np.einsum('...i,ij,...j->...', u, m, delta))
    matrix = (np.sqrt(integ_weights[:, None]*integ_weights[None, :])
              * np.linalg.det(chol)*norm*np.exp(exponent))
    h_err = float(np.linalg.norm(matrix-matrix.conj().T))
    assert h_err < 1e-10
    w = np.linalg.eigvalsh((matrix+matrix.conj().T)/2)
    raw_min_eigenvalue = float(w.min())
    assert w.min() > -1e-10
    assert abs(w.sum()-1) < 1e-10
    w = np.maximum(w, 0)
    return dict(order=order, entropy=float(-xlogy(w,w).sum()),
                purity=float((w*w).sum()), trace=float(w.sum()),
                raw_min_eigenvalue=raw_min_eigenvalue)


def thermal_entropy(nus):
    out = 0.
    tail = 0.
    for nu in nus:
        ratio = (nu-1)/(nu+1)
        probs = (1-ratio)*ratio**np.arange(256)
        out -= xlogy(probs,probs).sum()
        tail += ratio**256
    return float(out), float(tail)


def boson_checks(rng):
    results = []
    # Includes pure endpoint, degeneracy, and generic nonzero q-p correlations.
    for trial, nus in enumerate(([1.,1.,1.], [1.,1.25,1.25],
                                 [1.1,1.3,1.7], [2.,2.,2.])):
        h = rng.normal(size=(6,6))
        h = .10*(h+h.T)
        s = expm(om(3)@h)
        v = s@np.diag(np.repeat(nus,2))@s.T
        # Functional calculus on the raw covariance; no stored Williamson frame.
        generator = -om(3)@v
        j = generator@np.linalg.inv(sqrtm(-generator@generator))
        j = np.real_if_close(j).real
        assert np.linalg.norm(j@j+np.eye(6)) < 1e-9
        candidates = null_space(j[:2,2:])
        p = np.zeros(6)
        p[2:] = candidates[:,0]
        jp = j@p
        assert np.linalg.norm(jp[:2]) < 1e-10
        area = p@om(3)@jp
        assert area > 0
        plane = np.column_stack((p,jp))/np.sqrt(area)
        retained = null_space(plane[2:].T@om(2))
        retained[:,1] /= retained[:,0]@om(2)@retained[:,1]
        local = np.vstack((retained.T,plane[2:].T))
        transform = block_diag(np.eye(2),local)
        can_error = float(np.linalg.norm(transform@om(3)@transform.T-om(3)))
        assert can_error < 1e-9
        assert np.linalg.norm(transform[:2]-np.eye(6)[:2]) == 0
        newv = transform@v@transform.T
        reduced = newv[:4,:4]
        integral_errors = []
        for _ in range(12):
            q, qp = rng.normal(size=(2,2))
            integral_errors.append(abs(trace_last_kernel(newv,q,qp)-kernel(reduced,q,qp)))
        assert max(integral_errors) < 1e-11
        before, thermal_tail = thermal_entropy(nus)
        quadrature = [kernel_entropy(reduced,k) for k in (18,30,42)]
        after = quadrature[-1]['entropy']
        convergence = abs(after-quadrature[-2]['entropy'])
        assert convergence < 2e-7, (trial,quadrature)
        assert after <= before+2e-7, (before,after)
        purity_exact = 1/np.sqrt(np.linalg.det(reduced))
        purity_error = abs(quadrature[-1]['purity']-purity_exact)
        assert purity_error < 2e-8
        if trial == 0:
            assert abs(after) < 2e-10
            assert np.linalg.norm(newv[:4,4:]) < 1e-9
            assert abs(np.linalg.det(newv[4:,4:])-1) < 1e-9
        results.append(dict(trial=trial,nus=nus,before_thermal_probabilities=before,
            thermal_tail_probability=thermal_tail,after_kernel_entropy=after,
            drop=before-after,quadrature=quadrature,convergence_30_to_42=convergence,
            canonical_error=can_error,kernel_trace_max_error=float(max(integral_errors)),
            kernel_purity_error=float(purity_error),removed_purity=float(1/np.sqrt(np.linalg.det(newv[4:,4:]))),
            retained_removed_covariance_norm=float(np.linalg.norm(newv[:4,4:]))))
    return results


I = np.eye(2)
X = np.array([[0,1],[1,0]],complex)
Y = np.array([[0,-1j],[1j,0]],complex)
Z = np.diag([1.,-1.])


def majoranas(n):
    return [product([Z]*k+[a]+[I]*(n-k-1)) for k in range(n) for a in (X,Y)]


def cov_from_rho(rho,c):
    n = len(c)
    out = np.zeros((n,n))
    for i in range(n):
        for j in range(i+1,n):
            out[i,j] = np.real(1j*np.trace(rho@c[i]@c[j]))
            out[j,i] = -out[i,j]
    return out


def rotate_rho(rho,c,rng):
    # Each unitary is a two-term Clifford polynomial, not a matrix exponential.
    for _ in range(3*len(c)):
        i,j = rng.choice(len(c),2,replace=False)
        theta = rng.uniform(-2.5,2.5)
        unitary = np.cos(theta/2)*np.eye(len(rho))+np.sin(theta/2)*(c[i]@c[j])
        rho = unitary@rho@unitary.conj().T
    return rho


def spin_orthogonal(o,c):
    # Givens factorization O=G1^T ... Gr^T D; lift every planar rotation to Fock space.
    work = o.copy()
    unitary = np.eye(len(c[0]),dtype=complex)
    for col in range(len(o)-1):
        for row in range(len(o)-1,col,-1):
            a,b = work[col,col],work[row,col]
            if abs(b) < 1e-13:
                continue
            angle = np.arctan2(b,a)
            cc,ss = np.cos(angle),np.sin(angle)
            old = work[[col,row]].copy()
            work[col] = cc*old[0]+ss*old[1]
            work[row] = -ss*old[0]+cc*old[1]
            gate = np.cos(angle/2)*np.eye(len(unitary))-np.sin(angle/2)*(c[col]@c[row])
            unitary = unitary@gate
    assert np.linalg.norm(work-np.diag(np.diag(work))) < 1e-9
    negative = np.where(np.diag(work)<0)[0]
    assert len(negative)%2 == 0
    for i,j in negative.reshape(-1,2):
        unitary = unitary@(c[i]@c[j])
    action_error = max(np.linalg.norm(unitary.conj().T@c[i]@unitary
                                      -sum(o[i,j]*c[j] for j in range(len(c))))
                       for i in range(len(c)))
    assert action_error < 1e-8, action_error
    return unitary,float(action_error)


def trace_tail(rho,keep):
    first = 2**keep
    last = len(rho)//first
    return np.einsum('aibi->ab',rho.reshape(first,last,first,last))


def fermion_checks(rng):
    patterns = [[1.,1.,1.],[-1.,1.,1.],[0.,0.,0.],
                [0.,.4,1.],[.4,.4,-1.],[0.,1.,-1.],
                [0.,0.,1.,1.,-1.],[.3,.3,.3,.3,.3]]
    records = []
    for trial in range(32):
        biases = patterns[trial%len(patterns)]
        n = len(biases)
        a = (n-1)//2
        c = majoranas(n)
        rho0 = product([(I+b*Z)/2 for b in biases])
        rho = rotate_rho(rho0,c,rng)
        gamma = cov_from_rho(rho,c)
        vals,vecs = np.linalg.eigh(-gamma@gamma)
        nonzero = vals > 1e-10
        invmod = (vecs[:,nonzero]/np.sqrt(vals[nonzero]))@vecs[:,nonzero].T
        j = gamma@invmod
        zeros = vecs[:,~nonzero]
        assert zeros.shape[1]%2 == 0
        j += zeros@om(zeros.shape[1]//2)@zeros.T
        assert np.linalg.norm(j@j+np.eye(2*n)) < 1e-9
        assert np.linalg.norm(j.T+j) < 1e-9
        k = -j@gamma
        assert np.linalg.eigvalsh((k+k.T)/2).min() > -1e-9
        z = null_space(j[:2*a,2*a:])
        p = np.zeros(2*n)
        p[2*a:] = z[:,0]
        plane = np.column_stack((p,j@p))
        assert np.linalg.norm(plane[:2*a]) < 1e-9
        keep_c = null_space(plane[2*a:].T).T
        oc = np.vstack((keep_c,plane[2*a:].T))
        if np.linalg.det(oc)<0:
            oc[-1] *= -1
        o = block_diag(np.eye(2*a),oc)
        u,action_error = spin_orthogonal(o,c)
        newrho = u@rho@u.conj().T
        reduced = trace_tail(newrho,n-1)
        # The last mode is contiguous in the transformed algebra, so this is an actual trace.
        removed = np.einsum('aiaj->ij',newrho.reshape(2**(n-1),2,2**(n-1),2))
        before,after = ent(rho),ent(reduced)
        assert after <= before+2e-9
        physical_change = float(np.linalg.norm(trace_tail(rho,a)-trace_tail(newrho,a)))
        assert physical_change < 1e-9
        purity = float(np.real(np.trace(removed@removed)))
        if abs(before-after)<1e-9:
            assert abs(purity-1)<1e-8
            assert np.linalg.norm(newrho-np.kron(reduced,removed))<1e-8
        covariance_error = float(np.linalg.norm(cov_from_rho(newrho,c)-o@gamma@o.T))
        assert covariance_error < 1e-8
        records.append(dict(trial=trial,modes=n,n_X=a,biases=biases,
            entropy_before=before,entropy_after=after,drop=before-after,
            removed_density_purity=purity,clifford_action_error=action_error,
            physical_density_change=physical_change,covariance_error=covariance_error,
            zero_majorana_dimension=int(zeros.shape[1])))
    return records


def graded_permutation(n,order):
    matrix = np.zeros((2**n,2**n))
    newpos = np.argsort(order)
    for column in range(2**n):
        bits = [(column>>(n-1-i))&1 for i in range(n)]
        inv = sum(bits[i]*bits[j]*(newpos[i]>newpos[j]) for i in range(n) for j in range(i+1,n))
        newbits = [bits[i] for i in order]
        row = sum(bit<<(n-1-i) for i,bit in enumerate(newbits))
        matrix[row,column] = (-1)**inv
    return matrix


def entropy_cov_f(gamma):
    ev = np.linalg.eigvalsh(1j*gamma)
    p = np.clip((1+ev)/2,0,1)
    return float(-.5*np.sum(xlogy(p,p)+xlogy(1-p,1-p)))


def parity_checks(rng):
    c = majoranas(4)
    parity = product([Z]*4)
    permutation = graded_permutation(4,[0,2,1,3])
    keep_indices = [0,1,4,5]
    results = []
    for trial in range(12):
        b = [-1 if trial%2 else 1,1,1,1]
        rho = rotate_rho(product([(I+x*Z)/2 for x in b]),c,rng)
        # Auxiliary mode 2; its Majorana flips total parity, preserves AB, and is cut-local.
        rho2 = c[4]@rho@c[4]
        marginal_error = float(np.linalg.norm(trace_tail(rho,2)-trace_tail(rho2,2)))
        left = trace_tail(permutation@rho@permutation.T,2)
        left2 = trace_tail(permutation@rho2@permutation.T,2)
        before,after = ent(left),ent(left2)
        gamma = cov_from_rho(rho,c)
        covariance_entropy = entropy_cov_f(gamma[np.ix_(keep_indices,keep_indices)])
        p1,p2 = float(np.real(np.trace(parity@rho))),float(np.real(np.trace(parity@rho2)))
        assert marginal_error < 1e-12
        assert abs(before-after)<1e-11
        assert abs(before-covariance_entropy)<1e-10
        assert abs(p1+p2)<1e-11 and abs(abs(p1)-1)<1e-11
        results.append(dict(trial=trial,parity_before=p1,parity_after=p2,
            physical_marginal_error=marginal_error,graded_cut_entropy=before,
            parity_flipped_cut_entropy=after,covariance_entropy=covariance_entropy))
    return results


def main():
    rng = np.random.default_rng(SEED)
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),seed=SEED,
                  python=sys.version,executable=sys.executable,platform=platform.platform(),
                  packages={n:importlib.metadata.version(n) for n in ('numpy','scipy','sympy','mpmath')},
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  evidence_class='HEURISTIC NUMERICS; independent implementation and density representations')
    result['boson_kernel'] = boson_checks(rng)
    result['fermion_density'] = fermion_checks(rng)
    result['fermion_graded_parity'] = parity_checks(rng)
    result['overall'] = 'PASS'
    (ROOT/'independent_density_checks.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print('INDEPENDENT DENSITY CHECKS PASS')
    for b in result['boson_kernel']:
        print('BOSON', b['trial'], 'before', b['before_thermal_probabilities'],
              'after',b['after_kernel_entropy'],'convergence',b['convergence_30_to_42'])
    print('FERMION',len(result['fermion_density']),'cases; GRADED PARITY',len(result['fermion_graded_parity']),'cases')
    print('Max Clifford action error',max(t['clifford_action_error'] for t in result['fermion_density']))
    print('Max density physical marginal change',max(t['physical_density_change'] for t in result['fermion_density']))


if __name__ == '__main__':
    main()
