import Gaussian.Physical.Fermion.MarginalExtension
import Gaussian.Physical.Fermion.SuffixRestriction
import Gaussian.Physical.Fermion.Factorization

/-! Exact actual-state deletion after a pure trailing CAR block has been
identified.  Purity of that block is an explicit derived condition, not a
claim that every arbitrary selected auxiliary block is pure. -/
noncomputable section
open scoped MState
namespace Gaussian.Physical.Fermion

/-- In an actual pure state, purity of the genuine complementary density
forces purity of the retained actual density. -/
theorem prefixRestriction_pure_of_pure_suffix (k l : ℕ) (σ : Density (l+k))
    (hσ : ∃ ψ,σ=MState.pure ψ)
    (hs : ∃ ψ,suffixRestriction k l σ=MState.pure ψ) :
    ∃ ψ,prefixRestriction k l σ=MState.pure ψ := by
  let τ := σ.relabel (occupationSplit k l).symm
  have hp : ∃ ψ,τ=MState.pure ψ := by
    obtain ⟨ψ,rfl⟩ := hσ
    exact MState.relabel_pure_exists ψ _
  have hr : ∃ ψ,τ.traceLeft=MState.pure ψ := hs
  have hfac := pure_density_factors_of_pure_right τ hp hr
  have hpurity := (MState.pure_iff_purity_one τ).mp hp
  rw [hfac,MState.purity_prod,(MState.pure_iff_purity_one τ.traceLeft).mp hr,mul_one] at hpurity
  exact (MState.pure_iff_purity_one τ.traceRight).mpr hpurity

theorem prefixRestriction_pureQuasifree_of_pure_suffix (k l : ℕ) (σ : Density (l+k))
    (hσ : IsPureQuasifree σ)
    (hs : ∃ ψ,suffixRestriction k l σ=MState.pure ψ) :
    IsPureQuasifree (prefixRestriction k l σ) :=
  ⟨isQuasifree_prefixRestriction k l σ hσ.1,prefixRestriction_pure_of_pure_suffix k l σ hσ.2 hs⟩

/-- Equality-case covariance purity of the actual trailing CAR marginal is
sufficient to delete it, using the proved Wick purity bridge. -/
theorem prefixRestriction_pureQuasifree_of_suffix_covariancePure (k l : ℕ) (σ : Density (l+k))
    (hσ : IsPureQuasifree σ) (hs : CovariancePure (suffixRestriction k l σ)) :
    IsPureQuasifree (prefixRestriction k l σ) :=
  prefixRestriction_pureQuasifree_of_pure_suffix k l σ hσ
    ((quasifree_pure_iff_covariancePure l _ (isQuasifree_suffixRestriction k l σ hσ.1)).mpr hs)

/-- Deleting a pure final B' block preserves the physical state and the entire
AA' density exactly.  This is the state-level optimal-deletion operation. -/
theorem exists_sidewise_pure_B_deletion (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+(mB+extra))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA (mB+extra) ρ σ)
    (hs : CovariancePure (suffixRestriction ((mA+mB)+(nA+nB)) extra
      (modeCountCast (by omega) σ))) :
    ∃ τ : Density ((mA+mB)+(nA+nB)),IsSidewisePurifier nA nB mA mB ρ τ ∧
      sidewiseRestriction nA nB mA mB τ=sidewiseRestriction nA nB mA (mB+extra) σ := by
  let N := (mA+mB)+(nA+nB)
  have hcount : extra+N=(mA+(mB+extra))+(nA+nB) := by dsimp [N]; omega
  let big := modeCountCast hcount.symm σ
  have hbig : IsPureQuasifree big := modeCountCast_isPureQuasifree hcount.symm σ hσ.1
  let τ := prefixRestriction N extra big
  have hτ : IsPureQuasifree τ :=
    prefixRestriction_pureQuasifree_of_suffix_covariancePure N extra big hbig hs
  have hPhys := preservedPrefix_physicalMarginal (nA+nB) (mA+mB) extra (mA+(mB+extra))
    hcount τ big hτ.1 hbig.1 rfl
  have hPhys' : prefixRestriction (nA+nB) (mA+(mB+extra)) σ =
      prefixRestriction (nA+nB) (mA+mB) τ := by
    simpa only [big,modeCountCast_trans,modeCountCast_rfl] using hPhys
  have hCut := preservedPrefix_sidewiseRestriction nA nB mA mB extra hcount τ big hτ.1 hbig.1 rfl
  refine ⟨τ,⟨hτ,hPhys'.symm.trans hσ.2⟩,?_⟩
  symm
  simpa only [big,modeCountCast_trans,modeCountCast_rfl] using hCut

/-- The deletion operation preserves the actual entropy objective exactly. -/
theorem exists_sidewise_pure_B_entropy_deletion (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+(mB+extra))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA (mB+extra) ρ σ)
    (hs : CovariancePure (suffixRestriction ((mA+mB)+(nA+nB)) extra
      (modeCountCast (by omega) σ))) :
    ∃ τ : Density ((mA+mB)+(nA+nB)),IsSidewisePurifier nA nB mA mB ρ τ ∧
      sidewiseEntropy nA nB mA mB τ=sidewiseEntropy nA nB mA (mB+extra) σ := by
  obtain ⟨τ,hτ,he⟩ := exists_sidewise_pure_B_deletion nA nB mA mB extra ρ σ hσ hs
  exact ⟨τ,hτ,congrArg Sᵥₙ he⟩

end Gaussian.Physical.Fermion
