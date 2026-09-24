"""Fock-space oracle for the entropy-compression construction, independent of
Gaussian entropy evaluation. Small systems only; not a dimension cutoff in proof."""
from pathlib import Path
import json
import numpy as np
from scipy.linalg import expm,logm,block_diag
from scipy.special import xlogy
from verify_polar_compression import local_plane,omega,sf
ROOT=Path(__file__).resolve().parent
I=np.eye(2);X=np.array([[0.,1.],[1.,0.]]);Y=np.array([[0.,-1j],[1j,0.]]);Z=np.diag([1.,-1.])
def kronall(ops):
    r=np.array([[1.]],dtype=complex)
    for a in ops:r=np.kron(r,a)
    return r

def majoranas(n):
    return [kronall([Z]*j+[o]+[I]*(n-j-1)) for j in range(n) for o in [X,Y]]

def density_from_thermal_frame(Q,nu,c):
    # This uses the quadratic density operator, not a covariance entropy formula.
    B=Q@block_diag(*[np.arctanh(v)*np.array([[0.,1.],[-1.,0.]]) for v in nu])@Q.T
    H=np.zeros_like(c[0])
    for i in range(len(c)):
      for j in range(i+1,len(c)):H+=1j*B[i,j]*(c[i]@c[j])
    H=(H+H.conj().T)/2
    w,U=np.linalg.eigh(H);r=(U*np.exp(w-w.max()))@U.conj().T
    return r/np.trace(r)

def entropy_rho(r):
    w=np.linalg.eigvalsh((r+r.conj().T)/2)
    if w[0]<-1e-10:raise ValueError(w[0])
    w=np.maximum(w,0)
    return float(-np.sum(xlogy(w,w)))

def run():
    rng=np.random.default_rng(619257);out=[]
    for s in range(40):
      na=1+s%2;nc=na+1;n=na+nc;N=2*n
      Q=np.linalg.qr(rng.normal(size=(N,N)))[0]
      nu=rng.uniform(.04,.92,n)
      G=Q@block_diag(*[x*np.array([[0.,1.],[-1.,0.]]) for x in nu])@Q.T
      J=Q@omega(n)@Q.T
      P,T=local_plane(J,na)
      O=np.vstack((T,P.T))
      # Convert the full local-C orthogonal frame to SO without changing subspaces.
      if np.linalg.det(O)<0:O[-1]*=-1
      assert np.linalg.norm(O@O.T-np.eye(N))<1e-10
      assert np.linalg.norm(O[:2*na]-np.eye(N)[:2*na])<1e-10
      c=majoranas(n);r=density_from_thermal_frame(Q,nu,c)
      Grebuilt=np.zeros_like(G)
      for i in range(N):
       for j in range(i+1,N):Grebuilt[i,j]=np.real(1j*np.trace(r@c[i]@c[j]));Grebuilt[j,i]=-Grebuilt[i,j]
      assert np.linalg.norm(G-Grebuilt)<1e-9
      L=logm(O)
      assert np.max(abs(L.imag))<1e-9
      L=(L.real-L.real.T)/2
      assert np.linalg.norm(expm(L)-O)<1e-9
      K=np.zeros_like(r)
      for i in range(N):
       for j in range(i+1,N):K+=.5*L[i,j]*(c[i]@c[j])
      U=expm(K)
      act=max(np.linalg.norm(U.conj().T@c[i]@U-sum(O[i,j]*c[j] for j in range(N))) for i in range(N))
      assert act<1e-8
      rr=U@r@U.conj().T
      dim=2**(n-1)
      reduced=np.einsum('aibi->ab',rr.reshape(dim,2,dim,2))
      bef=entropy_rho(r);aft=entropy_rho(reduced)
      cov_bef=sf(G);cov_aft=sf(T@G@T.T)
      assert abs(bef-cov_bef)<1e-9 and abs(aft-cov_aft)<1e-9
      assert aft<=bef+1e-9
      out.append({'case':s,'modes':n,'density_entropy_before':bef,'density_entropy_after':aft,
                  'covariance_error':float(np.linalg.norm(G-Grebuilt)),
                  'unitary_action_error':float(act),'entropy_error':max(abs(bef-cov_bef),abs(aft-cov_aft))})
    (ROOT/'fock_compression_checks.json').write_text(json.dumps(out,indent=2))
    print('FOCK-SPACE CHECK PASS',len(out),'cases')
    print('max covariance error',max(x['covariance_error'] for x in out))
    print('max entropy error',max(x['entropy_error'] for x in out))
if __name__=='__main__':run()
