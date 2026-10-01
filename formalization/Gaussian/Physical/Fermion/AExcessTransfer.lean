import Gaussian.Physical.Fermion.LastAResplit
import Gaussian.Physical.Fermion.SidewiseLocalLift
import Gaussian.Physical.Fermion.CountedCutSelection

/-! Unconditional physical one-mode entropy compression at an A' excess.
The actual local adapted plane, protected orthogonal action, global lift and
signed complete-mode transfer are all constructed by the checked chain. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- An A'-excess purifier admits a genuine one-mode transfer to B' with no
entropy increase. Exact equality forces the transferred actual terminal mode
state to be pure. All parity components and zero physical parties remain. -/
theorem exists_A_excess_transfer (nA nB a b : ℕ) (hexcess : nA<a+1)
    (ρ : Density (nA+nB)) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB (a+1) b ρ σ) :
    ∃ τ : Density ((a+(b+1))+(nA+nB)),IsSidewisePurifier nA nB a (b+1) ρ τ ∧
      sidewiseEntropy nA nB a (b+1) τ≤sidewiseEntropy nA nB (a+1) b σ ∧
      (sidewiseEntropy nA nB a (b+1) τ=sidewiseEntropy nA nB (a+1) b σ →
        ∃ ψ,suffixRestriction ((a+b)+(nA+nB)) 1 (modeCountCast (by omega) τ)=MState.pure ψ) := by
  have hk : nA+(a+1)=1+(nA+a) := by omega
  let β := modeCountCast hk (sidewiseRestriction nA nB (a+1) b σ)
  have hβ : IsQuasifree β := modeCountCast_isQuasifree hk _
    (sidewiseRestriction_isQuasifree nA nB (a+1) b σ hσ.1.1)
  obtain ⟨R,U,hU,hfix,hle,heq⟩ := exists_counted_entropy_selection nA (nA+a) (by omega) β hβ
  have hfix' : ∀ i : MajoranaIndex (1+(nA+a)),i.1.val<nA →
      R (coefficientBasis _ i)=coefficientBasis _ i :=
    initialBasis_fixed_of_castLE nA (1+(nA+a)) (by omega) R hfix
  obtain ⟨σ',hσ',hPrefix,_hSuffix,_hEntropy⟩ :=
    exists_sidewise_local_state nA nB (a+1) b (1+(nA+a)) hk ρ σ hσ R U hU hfix'
  let τ := lastATransferState nA nB a b σ'
  have hτ : IsSidewisePurifier nA nB a (b+1) ρ τ :=
    lastATransfer_preserves_purifier nA nB a b ρ σ' hσ'
  have hc : sidewiseEntropy nA nB a (b+1) τ =
      Sᵥₙ (prefixRestriction (nA+a) 1 (β.uConj U)) := by
    unfold sidewiseEntropy
    dsimp only [τ]
    rw [lastATransfer_retained nA nB a b σ' hσ'.1.1,hPrefix]
  have ho : Sᵥₙ β=sidewiseEntropy nA nB (a+1) b σ := modeCountCast_entropy hk _
  refine ⟨τ,hτ,?_,?_⟩
  · rw [hc,← ho]
    exact hle
  · intro hcost
    have he : Sᵥₙ (prefixRestriction (nA+a) 1 (β.uConj U))=Sᵥₙ β := by
      rw [← hc,ho]
      exact hcost
    obtain ⟨ψ,hψ⟩ := heq he
    refine ⟨ψ,?_⟩
    dsimp only [τ]
    rw [lastATransfer_suffix nA nB a b σ' hσ'.1.1,hPrefix]
    exact hψ

/-- Equivalent equality callback in the actual covariance-purity interface
used by the exact finite-total deletion theorem. -/
theorem exists_A_excess_transfer_covariance (nA nB a b : ℕ) (hexcess : nA<a+1)
    (ρ : Density (nA+nB)) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB (a+1) b ρ σ) :
    ∃ τ : Density ((a+(b+1))+(nA+nB)),IsSidewisePurifier nA nB a (b+1) ρ τ ∧
      sidewiseEntropy nA nB a (b+1) τ≤sidewiseEntropy nA nB (a+1) b σ ∧
      (sidewiseEntropy nA nB a (b+1) τ=sidewiseEntropy nA nB (a+1) b σ →
        CovariancePure (suffixRestriction ((a+b)+(nA+nB)) 1 (modeCountCast (by omega) τ))) := by
  obtain ⟨τ,hτ,hle,hpure⟩ := exists_A_excess_transfer nA nB a b hexcess ρ σ hσ
  refine ⟨τ,hτ,hle,?_⟩
  intro he
  exact (quasifree_pure_iff_covariancePure 1 _ (isQuasifree_suffixRestriction _ _ _
    (modeCountCast_isQuasifree _ τ hτ.1.1))).mp (hpure he)

end Gaussian.Physical.Fermion
