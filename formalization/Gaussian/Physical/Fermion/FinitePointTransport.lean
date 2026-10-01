import Gaussian.Physical.Fermion.AllFiniteDomain

set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

def finitePurifierOfSidewiseAtTotal (nA nB mA mB M : ℕ) (h : mA+mB=M)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ) : FinitePurifier nA nB ρ M := by
  subst M
  exact finitePurifierOfSidewise nA nB mA mB ρ σ hσ

theorem finitePurifierOfSidewiseAtTotal_index (nA nB mA mB M : ℕ) (h : mA+mB=M)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    (finitePurifierOfSidewiseAtTotal nA nB mA mB M h ρ σ hσ).val.1.val=mA := by
  subst M
  rfl

theorem finitePurifierOfSidewiseAtTotal_cost (nA nB mA mB M : ℕ) (h : mA+mB=M)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    finitePurifierCost nA nB ρ M (finitePurifierOfSidewiseAtTotal nA nB mA mB M h ρ σ hσ)=
      sidewiseEntropy nA nB mA mB σ := by
  subst M
  exact finitePurifierOfSidewise_cost nA nB mA mB ρ σ hσ

theorem finitePurifier_asSidewise (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (p : FinitePurifier nA nB ρ M) :
    ∃ (mA mB : ℕ) (σ : Density ((mA+mB)+(nA+nB))),
      mA+mB=M ∧ mA=p.val.1.val ∧ IsSidewisePurifier nA nB mA mB ρ σ ∧
      sidewiseEntropy nA nB mA mB σ=finitePurifierCost nA nB ρ M p := by
  let j := p.val.1.val
  have hj : j≤M := by have h:=p.val.1.isLt; dsimp [j]; omega
  let h : M+(nA+nB)=(j+(M-j))+(nA+nB) := by omega
  refine ⟨j,M-j,modeCountCast h p.val.2,by omega,rfl,?_,rfl⟩
  refine ⟨modeCountCast_isPureQuasifree h p.val.2 p.property.1,?_⟩
  rw [prefixRestriction_cast_aux,p.property.2]

end Gaussian.Physical.Fermion
