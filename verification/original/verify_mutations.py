"""Deliberately false variants of the proof lemmas must be rejected.
A PASS here means the counterexample to the mutated claim was detected.
This is not automated verification of the full mathematical proof.
"""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import block_diag,expm,null_space
from verify_polar_compression import sf,sb,omega,local_plane
ROOT=Path(__file__).resolve().parent;out=[]
I2=np.eye(2);J=omega(1);Z=np.diag([1.,-1.])
def record(name,condition,detail):
    if not condition:raise AssertionError(name)
    out.append({'mutation':name,'result':'REJECTED AS REQUIRED','evidence':detail})
    print('MUTATION REJECTED',name)

G=np.block([[np.zeros((2,2)),I2],[-I2,np.zeros((2,2))]])
record('Fermion: omit strict c>a dimension condition',sf(G[:2,:2])>sf(G)+.6,
       {'full_entropy':sf(G),'after_deletion':sf(G[:2,:2])})
V=np.block([[(5/3)*I2,(4/3)*Z],[(4/3)*Z,(5/3)*I2]])
record('Boson: omit strict c>a dimension condition',sb(V[:2,:2])>sb(V)+.5,
       {'full_entropy':sb(V),'after_deletion':sb(V[:2,:2])})
G3=block_diag(G,J);keep=[0,1,4,5]
record('Fermion: arbitrary auxiliary plane instead of polar-invariant plane',
       sf(G3[np.ix_(keep,keep)])>sf(G3)+.6,{'n_X':1,'n_C':2,'deleted_mode':'entangled C1'})
V3=block_diag(V,I2)
record('Boson: arbitrary auxiliary plane instead of compatible-J plane',
       sb(V3[np.ix_(keep,keep)])>sb(V3)+.5,{'n_X':1,'n_C':2,'deleted_mode':'entangled C1'})
O=np.block([[I2,I2],[-I2,I2]])/np.sqrt(2);Gwrong=O@block_diag(J,-J)@O.T
K=-omega(2)@Gwrong
record('Fermion: use unrelated J with nonpositive polar modulus',
       np.linalg.eigvalsh(K)[0]<-.99 and sf(Gwrong[:2,:2])>sf(Gwrong)+.6,
       {'K_eigenvalues':np.linalg.eigvalsh(K).tolist()})
rng=np.random.default_rng(13579);H=rng.normal(size=(6,6));H=(H+H.T)*.3
S=expm(omega(3)@H);Jb=-np.linalg.solve(S.T,omega(3)@S.T);P,T=local_plane(Jb,1,omega(3))
wrongR=null_space(P[2:].T).T;wrongT=block_diag(I2,wrongR)
res=float(np.linalg.norm(wrongT@omega(3)@P))
record('Boson: Euclidean complement in original squeezed coordinates',res>1e-3,
       {'nonzero_cross_commutator_norm':res})
R=np.array([[1.,0,0,0],[0,0,1.,0]])
record('Boson: admit degenerate symplectic cuts',np.linalg.matrix_rank(R@omega(2)@R.T)==0,
       {'restricted_symplectic_rank':0,'required_rank':2})
GX=block_diag(J,.3*J,.3*J)
record('Discard a mixed auxiliary from a nonoptimal purification without equality',
       sf(GX[:4,:4])<sf(GX)-.5 and sf(.3*J)>.5,
       {'entropy_drop':sf(GX)-sf(GX[:4,:4]),'removed_mode_entropy':sf(.3*J)})
vals=[]
for e in [.1,.01,.001]:vals.append(sb(e*I2,e*J))
record('Boson: remove fixed positive covariance lower bound from coercivity',
       max(abs(x) for x in vals)<1e-12,
       {'epsilon':[.1,.01,.001],'entropy':vals,'covariance_minimum_also_tends_to_zero':True})
(ROOT/'mutation_checks.json').write_text(json.dumps(out,indent=2))
print('MUTATION SUITE PASS',len(out),'false variants rejected')
