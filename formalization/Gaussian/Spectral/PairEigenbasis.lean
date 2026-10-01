import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-! Parameter-free, unnormalized complex eigenbasis for canonical real mode pairs. -/
noncomputable section
open Module
open scoped Matrix
namespace Gaussian.Spectral

/-- Pairwise complex change of basis with columns (1,-i) and (1,i).
Normalization is unnecessary for characteristic-polynomial spectral transport. -/
def pairEigenEquiv (n : ℕ) : ((Fin n × Bool) → ℂ) ≃ₗ[ℂ] ((Fin n × Bool) → ℂ) where
  toFun z p := if p.2 then Complex.I*(z (p.1,true)-z (p.1,false)) else z (p.1,false)+z (p.1,true)
  invFun z p := if p.2 then (z (p.1,false)-Complex.I*z (p.1,true))/2
    else (z (p.1,false)+Complex.I*z (p.1,true))/2
  left_inv z := by
    ext ⟨i,b⟩
    cases b <;> dsimp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  right_inv z := by
    ext ⟨i,b⟩
    cases b <;> dsimp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  map_add' z w := by
    ext ⟨i,b⟩
    cases b <;> simp <;> ring
  map_smul' r z := by
    ext ⟨i,b⟩
    cases b <;> simp <;> ring

def pairEigenbasis (n : ℕ) : Basis ((Fin n × Bool)) ℂ ((Fin n × Bool) → ℂ) :=
  (Pi.basisFun ℂ ((Fin n × Bool))).map (pairEigenEquiv n)

theorem pairEigenbasis_apply (n : ℕ) (i j : Fin n) (a b : Bool) :
    pairEigenbasis n (i,a) (j,b) =
      if i=j then (if b then (if a then Complex.I else -Complex.I) else 1) else 0 := by
  rw [pairEigenbasis,Basis.map_apply,Pi.basisFun_apply]
  change (if b then Complex.I*((Pi.single (i,a) (1:ℂ) : (Fin n × Bool) → ℂ) (j,true)-
      (Pi.single (i,a) (1:ℂ) : (Fin n × Bool) → ℂ) (j,false)) else
      (Pi.single (i,a) (1:ℂ) : (Fin n × Bool) → ℂ) (j,false)+(Pi.single (i,a) (1:ℂ) : (Fin n × Bool) → ℂ) (j,true)) = _
  cases a <;> cases b <;> by_cases h : i=j <;> simp [Pi.single_apply,h,eq_comm]

end Gaussian.Spectral
