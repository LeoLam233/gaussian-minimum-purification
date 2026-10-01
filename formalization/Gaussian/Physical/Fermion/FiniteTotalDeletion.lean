import Gaussian.Physical.Fermion.PureDeletion
import Gaussian.Physical.Fermion.FiniteTotalDomain
import Gaussian.Physical.Fermion.SidewiseCountTransport

/-! The exact finite-total state deletion operation.  A preceding optimality
argument must prove purity of the selected final B' covariance; it is not
postulated for arbitrary feasible points. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- If a feasible point has a final B' mode whose actual CAR covariance is
pure, it gives a feasible point with one fewer auxiliary mode and exactly the
same actual AA' entropy. -/
theorem finitePurifier_delete_last_B (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (p : FinitePurifier nA nB ρ (M+1)) (hj : p.val.1.val≤M)
    (hs : CovariancePure (suffixRestriction (M+(nA+nB)) 1
      (modeCountCast (by omega) p.val.2))) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q=finitePurifierCost nA nB ρ (M+1) p := by
  let j := p.val.1.val
  have hsource : (M+1)+(nA+nB)=(j+((M-j)+1))+(nA+nB) := by dsimp [j]; omega
  let σ := modeCountCast hsource p.val.2
  have hσ : IsSidewisePurifier nA nB j ((M-j)+1) ρ σ := by
    refine ⟨modeCountCast_isPureQuasifree hsource p.val.2 p.property.1,?_⟩
    change prefixRestriction (nA+nB) (j+((M-j)+1)) (modeCountCast hsource p.val.2)=ρ
    rw [prefixRestriction_cast_aux,p.property.2]
  have hsize : (j+(M-j))+(nA+nB)=M+(nA+nB) := by dsimp [j]; omega
  have hpure : CovariancePure (suffixRestriction ((j+(M-j))+(nA+nB)) 1
      (modeCountCast (by dsimp [j]; omega) σ)) := by
    dsimp only [σ]
    rw [modeCountCast_trans]
    rw [suffixRestriction_cast_prefix_eq hsize _ (by omega) p.val.2]
    exact hs
  obtain ⟨τ,hτ,he⟩ := exists_sidewise_pure_B_entropy_deletion nA nB j (M-j) 1 ρ σ hσ hpure
  let q : FinitePurifier nA nB ρ M :=
    ⟨(⟨j,by dsimp [j]; omega⟩,modeCountCast hsize τ),
      modeCountCast_isPureQuasifree hsize τ hτ.1,
      by rw [prefixRestriction_cast_aux,hτ.2]⟩
  refine ⟨q,?_⟩
  have hB : (M+1)-p.val.1.val=(M-p.val.1.val)+1 := by omega
  change finiteTotalEntropy nA nB M ⟨j,by dsimp [j]; omega⟩ (modeCountCast hsize τ) =
    finiteTotalEntropy nA nB (M+1) p.val.1 p.val.2
  calc
    _ = sidewiseEntropy nA nB j (M-j) τ := by
      simp only [finiteTotalEntropy,modeCountCast_trans,modeCountCast_rfl]
    _ = sidewiseEntropy nA nB j ((M-j)+1) σ := he
    _ = finiteTotalEntropy nA nB (M+1) p.val.1 p.val.2 :=
      (sidewiseEntropy_cast_B_eq nA nB j hB _ hsource p.val.2).symm

/-- A nonincreasing fixed-total selection ending in a pure final B' mode is
sufficient for the sector-specific one-step finite descent. -/
theorem finitePurifier_delete_after_selection (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (p p' : FinitePurifier nA nB ρ (M+1))
    (hcost : finitePurifierCost nA nB ρ (M+1) p'≤finitePurifierCost nA nB ρ (M+1) p)
    (hj : p'.val.1.val≤M)
    (hs : CovariancePure (suffixRestriction (M+(nA+nB)) 1
      (modeCountCast (by omega) p'.val.2))) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q≤finitePurifierCost nA nB ρ (M+1) p := by
  obtain ⟨q,hq⟩ := finitePurifier_delete_last_B nA nB ρ M p' hj hs
  exact ⟨q,hq.le.trans hcost⟩

end Gaussian.Physical.Fermion
