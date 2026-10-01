import Gaussian.Physical.Fermion.ModeSelection
import Gaussian.Physical.Fermion.SidewiseIndices
import Gaussian.Physical.Fermion.CountTransport

/-! Exact actual marginal bookkeeping under adding or removing final B' modes.
These statements require raw Wick closure but no global or factor purity. -/
noncomputable section
namespace Gaussian.Physical.Fermion

theorem preservedPrefix_physicalMarginal (k l extra L : ℕ)
    (hcount : extra+(l+k)=L+k) (σ : Density (l+k)) (τ : Density (extra+(l+k)))
    (hσ : IsQuasifree σ) (hτ : IsQuasifree τ) (hOld : prefixRestriction (l+k) extra τ=σ) :
    prefixRestriction k L (modeCountCast hcount τ)=prefixRestriction k l σ := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction k L _ (modeCountCast_isQuasifree hcount τ hτ))
    (isQuasifree_prefixRestriction k l σ hσ)
  intro a b
  rw [prefixRestriction_covariance,modeCountCast_covariance,prefixRestriction_covariance]
  have hi (a : MajoranaIndex k) :
      (Fin.cast hcount.symm (prefixIndex k L a.1),a.2) =
        (prefixIndex (l+k) extra (prefixIndex k l a.1),a.2) := by
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_cast,prefixIndex_val]
    · rfl
  rw [hi a,hi b,← prefixRestriction_covariance (l+k) extra τ
    (prefixIndex k l a.1,a.2) (prefixIndex k l b.1,b.2),hOld]

/-- A genuine prefix reduction deleting only final B' modes leaves the entire
AA' density unchanged; equivalently, every such extension preserves that cut. -/
theorem preservedPrefix_sidewiseRestriction (nA nB mA mB extra : ℕ)
    (hcount : extra+((mA+mB)+(nA+nB))=(mA+(mB+extra))+(nA+nB))
    (σ : Density ((mA+mB)+(nA+nB)))
    (τ : Density (extra+((mA+mB)+(nA+nB))))
    (hσ : IsQuasifree σ) (hτ : IsQuasifree τ)
    (hOld : prefixRestriction ((mA+mB)+(nA+nB)) extra τ=σ) :
    sidewiseRestriction nA nB mA (mB+extra) (modeCountCast hcount τ)=
      sidewiseRestriction nA nB mA mB σ := by
  apply quasifree_eq_of_covariance _ _
    (sidewiseRestriction_isQuasifree nA nB mA (mB+extra) _ (modeCountCast_isQuasifree hcount τ hτ))
    (sidewiseRestriction_isQuasifree nA nB mA mB σ hσ)
  intro a b
  rw [sidewiseRestriction_covariance,sidewiseRestriction_covariance]
  change covariance (modeCountCast hcount τ)
    (sidewiseSourceIndex nA nB mA (mB+extra) a.1,a.2)
    (sidewiseSourceIndex nA nB mA (mB+extra) b.1,b.2) =
    covariance σ (sidewiseSourceIndex nA nB mA mB a.1,a.2) (sidewiseSourceIndex nA nB mA mB b.1,b.2)
  rw [modeCountCast_covariance,sidewiseSourceIndex_padding nA nB mA mB extra a.1 hcount,
    sidewiseSourceIndex_padding nA nB mA mB extra b.1 hcount,
    ← prefixRestriction_covariance ((mA+mB)+(nA+nB)) extra τ
      (sidewiseSourceIndex nA nB mA mB a.1,a.2) (sidewiseSourceIndex nA nB mA mB b.1,b.2),hOld]

end Gaussian.Physical.Fermion
