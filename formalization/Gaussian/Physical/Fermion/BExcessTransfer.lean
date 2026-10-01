import Gaussian.Physical.Fermion.AExcessTransfer
import Gaussian.Physical.Fermion.PartySwap

/-! The B-excess branch uses the proved signed whole-party symmetry and actual
pure complementary entropy. It never substitutes an unsigned spin permutation. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Transfer one excess B′ mode into A′ without increasing actual AA′ entropy. -/
theorem exists_B_excess_transfer (nA nB a b : ℕ) (hexcess : nB<b+1)
    (ρ : Density (nA+nB)) (σ : Density ((a+(b+1))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB a (b+1) ρ σ) :
    ∃ τ : Density (((a+1)+b)+(nA+nB)),
      IsSidewisePurifier nA nB (a+1) b ρ τ ∧
      sidewiseEntropy nA nB (a+1) b τ≤sidewiseEntropy nA nB a (b+1) σ := by
  have hρ : IsQuasifree ρ := hσ.2 ▸
    isQuasifree_prefixRestriction (nA+nB) (a+(b+1)) σ hσ.1.1
  let σ' := partySwapState nA nB a (b+1) σ
  have hσ' := partySwapState_feasible nA nB a (b+1) ρ σ hσ
  obtain ⟨ω,hω,hle,heq⟩ := exists_A_excess_transfer nB nA b a hexcess
    (physicalPartySwap nA nB ρ) σ' hσ'
  let τ := partySwapState nB nA b (a+1) ω
  have hτ := partySwapState_feasible nB nA b (a+1) (physicalPartySwap nA nB ρ) ω hω
  rw [physicalPartySwap_twice nA nB ρ hρ] at hτ
  refine ⟨τ,hτ,?_⟩
  calc
    sidewiseEntropy nA nB (a+1) b τ = sidewiseEntropy nB nA b (a+1) ω :=
      partySwapState_entropy nB nA b (a+1) ω hω.1
    _ ≤ sidewiseEntropy nB nA (b+1) a σ' := hle
    _ = sidewiseEntropy nA nB a (b+1) σ := partySwapState_entropy nA nB a (b+1) σ hσ.1

end Gaussian.Physical.Fermion
