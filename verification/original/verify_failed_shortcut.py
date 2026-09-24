"""A counterexample to a discarded shortcut, NOT to the central conjecture.
Diagonalizing C alone need not expose an entropy-nonincreasing coordinate deletion.
The successful lemma uses the polar complex structure of XC, not that of C alone.
"""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import block_diag
from verify_polar_compression import sf,polar_f,local_plane
ROOT=Path(__file__).resolve().parent
J=np.array([[0.,1.],[-1.,0.]])
R=np.array([[1/np.sqrt(2),-1/np.sqrt(2),0],[1/np.sqrt(6),1/np.sqrt(6),-2/np.sqrt(6)]])
C=(999/1000)*np.kron(R,np.eye(2))
D=block_diag(*[k/10000*J for k in [1,2,3]])
G=np.block([[np.zeros((4,4)),C],[-C.T,D]])
S=sf(G);bad=[]
for j in range(3):
    keep=[k for k in range(10) if k not in [4+2*j,5+2*j]]
    v=sf(G[np.ix_(keep,keep)]);bad.append(v)
    assert v>S+.1
P,T=local_plane(polar_f(G),2);good=sf(T@G@T.T)
assert good<S
out={'formula':'A=0_4; C=(999/1000) R tensor I_2; D=diag(J,2J,3J)/10000',
     'R_rows':['(1,-1,0)/sqrt(2)','(1,1,-2)/sqrt(6)'],
     'exact_operator_norm_upper_bound':'999/1000+3/10000=9993/10000<1',
     'entropy_before':S,'coordinate_deletion_entropies':bad,'polar_deletion_entropy':good,
     'status':'counterexample to fixed-C-Williamson coordinate deletion only'}
(ROOT/'failed_shortcut.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
