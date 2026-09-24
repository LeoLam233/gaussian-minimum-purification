"""Exact rational checks of both complex-structure compression constructions.
These are algebraic regression instances, not a finite proof of the universal theorem."""
import json
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parent
J2=s.Matrix([[0,1],[-1,0]])
Om=s.diag(J2,J2,J2);I=s.eye(6);z=s.symbols('z')

def zero(M):return all(s.cancel(x)==0 for x in M)
def check(b,label):
    if not b:raise AssertionError(label)
    print('EXACT PASS',label)

def cayley(X):return (I-X/2).inv()*(I+X/2)

def compression_check(D,J,Cmap,label):
    # Cmap maps coefficient vectors into the diagonal, compatible-J frame.
    k=J[:2,2:].nullspace()
    v=s.zeros(6,1);v[2:,0]=k[0]
    P=v.row_join(J*v)
    check(zero(P[:2,:]),label+' plane contained in C')
    check(zero(J*P-P*s.Matrix([[0,-1],[1,0]])),label+' plane J invariant')
    Pt=Cmap*P
    Pi=Pt*(Pt.T*Pt).inv()*Pt.T
    check(zero(Pi-Pi.T) and zero(Pi*Pi-Pi),label+' orthogonal projection')
    check(zero(Pi*Om-Om*Pi),label+' complex-linear projection')
    U=I-Pi;Ku=U*D*U
    poly=s.Poly(s.cancel(Ku.charpoly(z).as_expr()/z**2),z)
    # Every complex eigenvalue occurs twice in the real representation.
    factors=s.factor_list(poly.as_expr())[1]
    check(all(e%2==0 for f,e in factors),label+' double real spectrum')
    q=s.Poly(s.prod(f**(e//2) for f,e in factors),z).monic()
    check(q.degree()==2,label+' two complex retained modes')
    roots=s.polys.polytools.intervals(q,eps=s.Rational(1,10**20))
    vals=sorted([D[0,0],D[2,2],D[4,4]])
    for j,((lo,hi),mult) in enumerate(roots):
        check(mult==1 and vals[j]<=lo and hi<=vals[j+1],label+f' exact interlacing {j}')
    return {'compressed_complex_characteristic_polynomial':str(q.as_expr()),
            'root_intervals':[[str(a),str(b)] for (a,b),m in roots],
            'full_spectrum':[str(v) for v in vals]}

def run():
    X=s.zeros(6)
    for i,j,r in [(0,2,s.Rational(1,3)),(1,4,s.Rational(1,4)),(2,5,s.Rational(1,5))]:X[i,j]=r;X[j,i]=-r
    Q=cayley(X)
    check(zero(Q.T*Q-I),'fermion rational orthogonality')
    D=s.diag(*[t for v in [s.Rational(1,5),s.Rational(2,5),s.Rational(4,5)] for t in [v,v]])
    G=Q*Om*D*Q.T;J=Q*Om*Q.T
    check(zero(J*J+I),'fermion J squared')
    check(zero(-J*G-Q*D*Q.T),'fermion positive polar modulus')
    ff=compression_check(D,J,Q.T,'fermion')
    H=s.zeros(6)
    for i,j,r in [(0,2,s.Rational(1,3)),(1,4,s.Rational(1,4)),(2,5,s.Rational(1,5))]:H[i,j]=H[j,i]=r
    S=cayley(Om*H)
    check(zero(S*Om*S.T-Om),'boson rational symplecticity')
    D=s.diag(1,1,2,2,4,4);V=S*D*S.T
    J=-S.T.inv()*Om*S.T
    check(zero(J*J+I),'boson J squared')
    check(zero(J.T*Om*J-Om),'boson J symplectic')
    check(zero(J.T*V*J-V),'boson covariance J invariant')
    check(zero(Om*J-S*S.T),'boson positive compatible metric')
    bb=compression_check(D,J,S.T,'boson')
    # Exact equality and strictness traces at purity boundaries.
    p=s.Matrix([0,0,1]);K=s.diag(s.Rational(1,5),s.Rational(2,5),1)
    check((p.T*K*p)[0]==1 and zero((s.eye(3)-K)*p),'fermion equality pure support')
    K=s.diag(1,2,4);p=s.Matrix([1,0,0])
    check((p.T*K*p)[0]==1 and zero((K-s.eye(3))*p),'boson equality pure support')
    (ROOT/'exact_geometry_checks.json').write_text(json.dumps({'fermion':ff,'boson':bb},indent=2))
    print('EXACT GEOMETRY CHECKS PASS')
if __name__=='__main__':run()
