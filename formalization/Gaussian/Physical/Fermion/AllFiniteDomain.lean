import Gaussian.Physical.Fermion.FiniteTotalDomain
import Gaussian.Physical.Fermion.SidewiseCountTransport

/-! The optimization domain is the union of actual pure Gaussian purifiers at
all finite sidewise auxiliary counts. Its objective is actual density entropy.
No size cap, canonical ansatz or chosen total parity is part of the definition. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Actual feasible entropy values for every finite A′ and B′ mode count. -/
def allFinitePurificationCosts (nA nB : ℕ) (ρ : Density (nA+nB)) : Set ℝ :=
  {c | ∃ (mA mB : ℕ) (σ : Density ((mA+mB)+(nA+nB))),
    IsSidewisePurifier nA nB mA mB ρ σ ∧ sidewiseEntropy nA nB mA mB σ=c}

def gaussianPurificationInfimum (nA nB : ℕ) (ρ : Density (nA+nB)) : ℝ :=
  sInf (allFinitePurificationCosts nA nB ρ)

def finitePurifierOfSidewise (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    FinitePurifier nA nB ρ (mA+mB) :=
  ⟨(⟨mA,by omega⟩,σ),hσ⟩

theorem finitePurifierOfSidewise_cost (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    finitePurifierCost nA nB ρ (mA+mB) (finitePurifierOfSidewise nA nB mA mB ρ σ hσ)=
      sidewiseEntropy nA nB mA mB σ := by
  change sidewiseEntropy nA nB mA ((mA+mB)-mA) (modeCountCast _ σ)=_
  exact sidewiseEntropy_cast_B_eq nA nB mA (by omega) _ rfl σ

theorem finitePurifier_cost_mem_allFinite (nA nB : ℕ) (ρ : Density (nA+nB))
    (M : ℕ) (p : FinitePurifier nA nB ρ M) :
    finitePurifierCost nA nB ρ M p ∈ allFinitePurificationCosts nA nB ρ := by
  let h : M+(nA+nB)=(p.val.1.val+(M-p.val.1.val))+(nA+nB) := by
    have hi := p.val.1.isLt
    omega
  refine ⟨p.val.1.val,M-p.val.1.val,modeCountCast h p.val.2,?_,rfl⟩
  refine ⟨modeCountCast_isPureQuasifree h p.val.2 p.property.1,?_⟩
  rw [prefixRestriction_cast_aux,p.property.2]

/-- Finite-total coding and the actual all-sidewise domain have exactly the same
feasible costs; in particular no larger auxiliary total is omitted. -/
theorem allFiniteCosts_iff_finitePurifier (nA nB : ℕ) (ρ : Density (nA+nB)) (c : ℝ) :
    c ∈ allFinitePurificationCosts nA nB ρ ↔
      ∃ (M : ℕ) (p : FinitePurifier nA nB ρ M),finitePurifierCost nA nB ρ M p=c := by
  constructor
  · rintro ⟨mA,mB,σ,hσ,rfl⟩
    exact ⟨mA+mB,finitePurifierOfSidewise nA nB mA mB ρ σ hσ,
      finitePurifierOfSidewise_cost nA nB mA mB ρ σ hσ⟩
  · rintro ⟨M,p,rfl⟩
    exact finitePurifier_cost_mem_allFinite nA nB ρ M p

/-- A genuine global actual witness identifies the all-finite infimum and
attains it. This wrapper requires that witness; it does not infer it from
fixed-size nonemptiness or fixed-size attainment. -/
theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ)
    (hmin : ∀ (a b : ℕ) (τ : Density ((a+b)+(nA+nB))),
      IsSidewisePurifier nA nB a b ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB a b τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy nA nB mA mB σ := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨mA,mB,σ,hσ,rfl⟩
  · rintro c ⟨a,b,τ,hτ,rfl⟩
    exact hmin a b τ hτ

end Gaussian.Physical.Fermion
