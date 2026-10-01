import Gaussian.Physical.Fermion.OptimalDeletion
import Gaussian.Physical.Fermion.MatchedSplit
import Gaussian.Physical.Fermion.FiniteTotalPadding

/-! Actual finite CAR Gaussian minimum purification, with all finite sidewise
auxiliary counts in the comparison and an attained matched-size witness. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

/-- The actual physical fermionic optimization theorem. The comparison includes
both possible definite total parities, every finite sidewise auxiliary count,
and all degenerate/zero/pure endpoints allowed by the raw Wick predicate. -/
theorem exists_matched_global_gaussian_purification (nA nB : ℕ)
    (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ=gaussianPurificationInfimum nA nB ρ ∧
      ∀ (mA mB : ℕ) (τ : Density ((mA+mB)+(nA+nB))),
        IsSidewisePurifier nA nB mA mB ρ τ →
          sidewiseEntropy nA nB nA nB σ≤sidewiseEntropy nA nB mA mB τ := by
  obtain ⟨p,hp⟩ := Gaussian.Optimization.global_attained_from_optimal_deletion
    (FinitePurifier nA nB ρ) (finitePurifierCost nA nB ρ) (nA+nB)
    (finitePurifier_attainment nA nB ρ hρ)
    (finitePurifier_optimal_delete nA nB ρ)
    (by
      intro M hM x
      obtain ⟨y,hy⟩ := finitePurifier_padding nA nB ρ M (nA+nB) (by omega) x
      exact ⟨y,hy.le⟩)
  obtain ⟨σ,hσ,hcost⟩ := finitePurifier_matchSplit nA nB ρ p
  have hmin : ∀ (mA mB : ℕ) (τ : Density ((mA+mB)+(nA+nB))),
      IsSidewisePurifier nA nB mA mB ρ τ →
        sidewiseEntropy nA nB nA nB σ≤sidewiseEntropy nA nB mA mB τ := by
    intro mA mB τ hτ
    have hh := hp (mA+mB) (finitePurifierOfSidewise nA nB mA mB ρ τ hτ)
    rw [finitePurifierOfSidewise_cost] at hh
    exact hcost.trans hh
  exact ⟨σ,hσ,(infimum_eq_of_global_sidewise_witness nA nB nA nB ρ σ hσ hmin).symm,hmin⟩

end Gaussian.Physical.Fermion
