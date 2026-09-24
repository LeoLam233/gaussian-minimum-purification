"""Independent constructive checks of the polar-complex-structure entropy lemma.
Numerical regression only: the accompanying analytic proof is not inferred from these tests.
"""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm, null_space, schur, block_diag
from scipy.special import xlogy

ROOT=Path(__file__).resolve().parent
J2=np.array([[0.,1.],[-1.,0.]])
def omega(n): return np.kron(np.eye(n),J2)
def hs(p):
    p=np.clip(p,0,1)
    return -xlogy(p,p)-xlogy(1-p,1-p)
def sf(G):
    eig=np.linalg.eigvalsh(1j*(G-G.T)/2)
    return float(.5*np.sum(hs((1+eig)/2)))
def sb(V,Om=None):
    if Om is None: Om=omega(len(V)//2)
    # Hermitian representative, independent of the earlier nonnormal eigensolver.
    d,U=np.linalg.eigh((V+V.T)/2)
    sqrt=(U*np.sqrt(d))@U.T
    vals=np.linalg.eigvalsh(1j*sqrt@np.linalg.inv(Om)@sqrt)
    nu=vals[len(V)//2:]
    if min(nu)<1-1e-7: raise ValueError(('nonphysical',nu))
    a=np.maximum((nu-1)/2,0)
    return float(np.sum(xlogy(a+1,a+1)-xlogy(a,a)))

def polar_f(G):
    # Real Schur handles zero singular values by an arbitrary complex structure.
    H,Q=schur(G,output='real')
    J=np.zeros_like(G)
    for k in range(len(G)//2):
        sign=1. if H[2*k,2*k+1]>=0 else -1.
        J[2*k:2*k+2,2*k:2*k+2]=sign*J2
    return Q@J@Q.T

def local_plane(J,na,Om=None):
    """Columns span a J-invariant plane contained in C=the last coordinates."""
    N=len(J);nc=(N-2*na)//2
    if nc<=na: raise ValueError('dimension guarantee requires n_C>n_A')
    ker=null_space(J[:2*na,2*na:],rcond=1e-10)
    v=np.zeros(N);v[2*na:]=ker[:,0]
    jv=J@v
    assert np.linalg.norm(jv[:2*na])<1e-8
    P=np.column_stack((v,jv))
    if Om is None:
        R=null_space(P[2*na:].T).T
    else:
        q=float(v@Om@jv)
        if q<=0: raise ValueError(('incompatible J',q))
        P=P/np.sqrt(q)
        R=null_space(P[2*na:].T@Om[2*na:,2*na:]).T
    T=np.zeros((N-2,N));T[:2*na,:2*na]=np.eye(2*na)
    T[2*na:,2*na:]=R
    return P,T

def run():
    rng=np.random.default_rng(39181753)
    records=[]
    worst={'fermion':-1.,'boson':-1.}
    for kind in ['fermion','boson']:
      for i in range(500):
        na=1+i%4;nc=na+1+(i//4)%4;n=na+nc;Om=omega(n)
        if kind=='fermion':
            Q=np.linalg.qr(rng.normal(size=(2*n,2*n)))[0]
            nu=rng.uniform(0,1,n)
            if i%5==0:nu[-min(3,n):]=1
            if i%7==0:nu[:min(2,n)]=0
            G=Q@block_diag(*[x*J2 for x in nu])@Q.T
            # Use known generating structure first, reconstructed Schur as separate check.
            J=Q@Om@Q.T
            P,T=local_plane(J,na)
            before=sf(G);after=sf(T@G@T.T)
            res=max(np.linalg.norm(J@J+np.eye(2*n)),np.linalg.norm(T@P))
            Jr=polar_f(G)
            # Nonzero random Schur blocks can be arranged next to null 1x1 blocks.
            # Verify, don't assume the arbitrary null-space pairing is valid.
            K=-Jr@G
            assert np.linalg.norm(Jr@Jr+np.eye(2*n))<1e-8
            assert np.linalg.norm(K-K.T)<1e-8
            assert np.linalg.eigvalsh((K+K.T)/2)[0]>-1e-8
            P2,T2=local_plane(Jr,na)
            assert sf(T2@G@T2.T)<=before+1e-8
            vals=np.sort(nu)
            spectral_bound=float(np.sum(hs((1-vals[:-1])/2)))
        else:
            H=rng.normal(size=(2*n,2*n));H=(H+H.T)*.12
            S=expm(Om@H)
            nu=1+np.exp(rng.uniform(-5,4,n))
            if i%5==0:nu[:min(3,n)]=1
            if i%7==0:nu[:]=1+1e-7*(nu-1)
            V=S@np.diag(np.repeat(nu,2))@S.T
            J=-np.linalg.solve(S.T,Om@S.T)
            P,T=local_plane(J,na,Om)
            before=sb(V);after=sb(T@V@T.T,T@Om@T.T)
            res=max(np.linalg.norm(J@J+np.eye(2*n)),np.linalg.norm(T@Om@P))
            # Williamson-frame interlacing bound.
            vv=np.sort(nu)[1:];a=(vv-1)/2
            spectral_bound=float(np.sum(xlogy(a+1,a+1)-xlogy(a,a)))
        if after>spectral_bound+2e-7 or after>before+2e-7:
            raise AssertionError((kind,i,before,after,spectral_bound))
        worst[kind]=max(worst[kind],after-before)
        records.append({'kind':kind,'i':i,'n_A':na,'n_C':nc,'before':before,'after':after,'bound':spectral_bound,'geometry_residual':res})
    # A strictness/equality check: an exactly pure and uncoupled C mode has zero loss.
    G=block_diag(.3*J2,.6*J2,J2); assert abs(sf(G)-sf(G[:4,:4]))<1e-14
    V=block_diag(2*np.eye(2),3*np.eye(2),np.eye(2)); assert abs(sb(V)-sb(V[:4,:4]))<1e-14
    out={'seed':39181753,'tests':len(records),'worst_after_minus_before':worst,'records':records}
    (ROOT/'polar_compression_checks.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
    print('POLAR COMPRESSION REGRESSION PASS')

if __name__=='__main__':run()
