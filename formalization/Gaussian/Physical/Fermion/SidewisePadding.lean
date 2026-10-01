import Gaussian.Physical.Fermion.ModeSelection
import Gaussian.Physical.Fermion.SidewiseIndices
import Gaussian.Physical.Fermion.CountTransport

/-! Actual entropy-preserving pure Gaussian padding on B'.  The proof preserves
the entire AA' density through its genuine covariance restriction, rather than
substituting an unsigned tensor permutation for the CAR cut. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Pure B' padding preserves both the AB physical density and the entire AA'
cut density exactly, so it preserves the actual optimization objective. -/
theorem exists_sidewise_B_padding (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    ∃ τ : Density ((mA+(mB+extra))+(nA+nB)),
      IsSidewisePurifier nA nB mA (mB+extra) ρ τ ∧
      sidewiseRestriction nA nB mA (mB+extra) τ=sidewiseRestriction nA nB mA mB σ := by
  let N := (mA+mB)+(nA+nB)
  have hcount : extra+N=(mA+(mB+extra))+(nA+nB) := by dsimp [N]; omega
  obtain ⟨τ,ψ,hτ,hOld,hProduct⟩ := exists_pure_quasifree_padding N extra σ hσ.1
  have hnew : IsPureQuasifree (modeCountCast hcount τ) := modeCountCast_isPureQuasifree hcount τ hτ
  refine ⟨modeCountCast hcount τ,⟨hnew,?_⟩,?_⟩
  · have hρ : IsQuasifree ρ := hσ.2 ▸ isQuasifree_prefixRestriction (nA+nB) (mA+mB) σ hσ.1.1
    apply quasifree_eq_of_covariance _ ρ
      (isQuasifree_prefixRestriction (nA+nB) (mA+(mB+extra)) _ hnew.1) hρ
    intro a b
    rw [prefixRestriction_covariance,modeCountCast_covariance]
    have hi (a : MajoranaIndex (nA+nB)) :
        (Fin.cast hcount.symm (prefixIndex (nA+nB) (mA+(mB+extra)) a.1),a.2) =
          (prefixIndex N extra (prefixIndex (nA+nB) (mA+mB) a.1),a.2) := by
      apply Prod.ext
      · apply Fin.ext; simp only [Fin.val_cast,prefixIndex_val]
      · rfl
    rw [hi a,hi b,← prefixRestriction_covariance N extra τ
      (prefixIndex (nA+nB) (mA+mB) a.1,a.2) (prefixIndex (nA+nB) (mA+mB) b.1,b.2),hOld,
      ← prefixRestriction_covariance (nA+nB) (mA+mB) σ a b,hσ.2]
  · apply quasifree_eq_of_covariance _ _
      (sidewiseRestriction_isQuasifree nA nB mA (mB+extra) _ hnew.1)
      (sidewiseRestriction_isQuasifree nA nB mA mB σ hσ.1.1)
    intro a b
    rw [sidewiseRestriction_covariance,sidewiseRestriction_covariance]
    change covariance (modeCountCast hcount τ)
      (sidewiseSourceIndex nA nB mA (mB+extra) a.1,a.2)
      (sidewiseSourceIndex nA nB mA (mB+extra) b.1,b.2) =
      covariance σ (sidewiseSourceIndex nA nB mA mB a.1,a.2) (sidewiseSourceIndex nA nB mA mB b.1,b.2)
    rw [modeCountCast_covariance,sidewiseSourceIndex_padding nA nB mA mB extra a.1 hcount,
      sidewiseSourceIndex_padding nA nB mA mB extra b.1 hcount,
      ← prefixRestriction_covariance N extra τ
        (sidewiseSourceIndex nA nB mA mB a.1,a.2) (sidewiseSourceIndex nA nB mA mB b.1,b.2),hOld]

theorem exists_sidewise_B_entropy_padding (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsSidewisePurifier nA nB mA mB ρ σ) :
    ∃ τ : Density ((mA+(mB+extra))+(nA+nB)),
      IsSidewisePurifier nA nB mA (mB+extra) ρ τ ∧
      sidewiseEntropy nA nB mA (mB+extra) τ=sidewiseEntropy nA nB mA mB σ := by
  obtain ⟨τ,hτ,he⟩ := exists_sidewise_B_padding nA nB mA mB extra ρ σ hσ
  exact ⟨τ,hτ,congrArg Sᵥₙ he⟩

end Gaussian.Physical.Fermion
