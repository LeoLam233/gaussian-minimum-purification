"""Check Gaussian purification orbit reconstruction, and an exact bosonic
entropy-divergent family approaching the nonsymplectic Grassmannian boundary."""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm,block_diag,null_space,schur
import sympy as sy
import mpmath as mp
ROOT=Path(__file__).resolve().parent
J=np.array([[0.,1.],[-1.,0.]])
Z=np.diag([1.,-1.])
def om(n):return np.kron(np.eye(n),J)

def extend_symplectic_rows(R):
    m=R.shape[1]//2;r=len(R)//2
    if r==m:return R
    B=null_space(R@om(m)).T
    H,O=schur(B@om(m)@B.T,output='real')
    A=np.zeros_like(H)
    for j in range(m-r):
        v=H[2*j,2*j+1]
        assert abs(v)>1e-10
        A[2*j,2*j]=1/np.sqrt(abs(v));A[2*j+1,2*j+1]=np.sign(v)/np.sqrt(abs(v))
    Q=A@O.T@B
    F=np.vstack([R,Q])
    assert np.linalg.norm(F@om(m)@F.T-om(m))<1e-7
    return F

def run():
    rng=np.random.default_rng(82500931);records=[]
    for kind in ['fermion','boson']:
      for it in range(100):
        n=2+it%4;r=1+it%n;m=n+it%3
        if kind=='fermion':
            nu=np.r_[rng.uniform(0,.95,r),np.ones(n-r)]
            G=block_diag(*[v*J for v in nu]);K=np.diag(np.repeat(np.sqrt(1-nu*nu),2))
            C=np.pad(K,((0,0),(0,2*(m-n))))
            D=block_diag(-G,*[J for _ in range(m-n)])
            Q=np.linalg.qr(rng.normal(size=(2*m,2*m)))[0]
            C=C@Q.T;D=Q@D@Q.T
            R=np.diag(1/np.repeat(np.sqrt(1-nu[:r]**2),2))@C[:2*r]
            F=np.vstack([R,null_space(R).T]) if r<m else R
            Cp=C@F.T;Dp=F@D@F.T
            target=np.zeros_like(Cp);target[:2*r,:2*r]=K[:2*r,:2*r]
            err=max(np.linalg.norm(Cp-target),np.linalg.norm(Dp[:2*r,:2*r]+G[:2*r,:2*r]),np.linalg.norm(Dp[:2*r,2*r:]))
            E=Dp[2*r:,2*r:]
            pure=np.linalg.norm(E@E+np.eye(len(E)))
        else:
            nu=np.r_[1+np.exp(rng.uniform(-2,2,r)),np.ones(n-r)]
            G=np.diag(np.repeat(nu,2));K=block_diag(*[np.sqrt(v*v-1)*Z for v in nu])
            C=np.pad(K,((0,0),(0,2*(m-n))))
            D=block_diag(G,np.eye(2*(m-n)))
            H=rng.normal(size=(2*m,2*m));H=(H+H.T)*.12
            Q=expm(om(m)@H)
            C=C@Q.T;D=Q@D@Q.T
            L=K[:2*r,:2*r];R=np.linalg.solve(L,C[:2*r])
            F=extend_symplectic_rows(R)
            U=np.linalg.inv(F).T
            Cp=C@U.T;Dp=U@D@U.T
            target=np.zeros_like(Cp);target[:2*r,:2*r]=L
            err=max(np.linalg.norm(Cp-target),np.linalg.norm(Dp[:2*r,:2*r]-G[:2*r,:2*r]),np.linalg.norm(Dp[:2*r,2*r:]))
            E=Dp[2*r:,2*r:];OE=om(m-r)
            pure=np.linalg.norm(E@OE@E-OE)
        assert err<2e-7 and pure<2e-7,(kind,it,err,pure)
        records.append({'kind':kind,'case':it,'physical_modes':n,'mixed_modes':r,'auxiliary_modes':m,
                        'canonical_reconstruction_error':float(err),'extra_purity_error':float(pure)})
    # Boundary family: A thermal mode, its purifier E1, and a thermal E2.
    e,z=sy.symbols('e z',positive=True)
    Os=sy.diag(sy.Matrix([[0,1],[-1,0]]),e*sy.Matrix([[0,1],[-1,0]]))
    Vs=sy.Matrix([[2,0,sy.sqrt(3),0],[0,2,0,-sy.sqrt(3)*e],
                  [sy.sqrt(3),0,2,0],[0,-sy.sqrt(3)*e,0,3-e**2]])
    expr=sy.factor((z*sy.eye(4)-sy.I*Os.inv()*Vs).det())
    expected=(z*z-1)*(z*z+5-6/e**2)
    assert sy.simplify(expr-expected)==0
    assert sy.factor(Vs.det())==6-5*e**2
    print('EXACT BOUNDARY CHARACTERISTIC POLYNOMIAL:',expr)
    mp.mp.dps=110
    def b(v):
        a=(v-1)/2
        return (a+1)*mp.log(a+1)-a*mp.log(a) if a else mp.mpf(0)
    boundary=[]
    for power in [1,5,15,30,50]:
        eps=mp.mpf(10)**(-power);v=mp.sqrt(6/eps**2-5)
        S=b(v);lower=(2-mp.sqrt(3))/eps
        assert v>=lower
        boundary.append({'epsilon':'1e-'+str(power),'nu_max':mp.nstr(v,60),'entropy_nats':mp.nstr(S,60),
                         'coercivity_lower_bound':mp.nstr(lower,60)})
    (ROOT/'orbit_and_boundary_checks.json').write_text(json.dumps({'seed':82500931,'orbit_records':records,
        'boundary_characteristic_polynomial':str(expr),'boundary':boundary},indent=2))
    print('ORBIT RECONSTRUCTION PASS',len(records),'cases')
    print('max reconstruction error',max(t['canonical_reconstruction_error'] for t in records))
    print('max extra purity error',max(t['extra_purity_error'] for t in records))
    for t in boundary:print('BOUNDARY',t['epsilon'],'entropy',t['entropy_nats'])
if __name__=='__main__':run()
