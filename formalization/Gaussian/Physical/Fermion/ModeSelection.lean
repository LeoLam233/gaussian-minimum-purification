import Gaussian.Physical.Fermion.SidewiseDomain
import Gaussian.Physical.Fermion.PaddingFeasibility

noncomputable section
namespace Gaussian.Physical.Fermion

theorem reindexCoefficient_single {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e] (q : d ≃ e) (a : d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ q (EuclideanSpace.single a 1) =
      EuclideanSpace.single (q a) 1 := by
  ext b
  simp only [LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft'_apply,PiLp.single_apply]
  change (if q.symm b=a then (1:ℝ) else 0) = (if b=q a then 1 else 0)
  congr 1
  exact propext q.symm_apply_eq

/-- The covariance of a genuinely implemented complete-mode permutation uses
its inverse mode labels, including all fermionic signs through Implements. -/
theorem permutationAction_covariance (n : ℕ) (p : Equiv.Perm (Fin n))
    (U : Matrix.unitaryGroup (Occupation n) ℂ)
    (hU : Implements n (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.prodCongr p (Equiv.refl Bool))) U)
    (ρ : Density n) (a b : MajoranaIndex n) :
    covariance (ρ.uConj U) a b = covariance ρ (p.symm a.1,a.2) (p.symm b.1,b.2) := by
  rw [← covarianceForm_basis,implemented_covarianceForm ρ _ U hU]
  simp only [LinearIsometryEquiv.inv_def,LinearIsometryEquiv.piLpCongrLeft_symm,
    coefficientBasis,reindexCoefficient_single,Equiv.prodCongr_symm,Equiv.refl_symm,
    Equiv.prodCongr_apply,Equiv.refl_apply]
  exact covarianceForm_basis ρ _ _

/-- Exact covariance source-label rule for the actual sidewise AA' marginal. -/
theorem sidewiseRestriction_covariance (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (a b : MajoranaIndex (nA+mA)) :
    covariance (sidewiseRestriction nA nB mA mB σ) a b =
      covariance σ
        ((sidewiseModePermutation nA nB mA mB).symm
          (Fin.cast (by omega) (prefixIndex (nA+mA) (nB+mB) a.1)),a.2)
        ((sidewiseModePermutation nA nB mA mB).symm
          (Fin.cast (by omega) (prefixIndex (nA+mA) (nB+mB) b.1)),b.2) := by
  unfold sidewiseRestriction selectedRestriction
  rw [prefixRestriction_covariance,modeCountCast_covariance]
  exact permutationAction_covariance _ _ _ (sidewiseUnitary_implements nA nB mA mB) σ _ _

end Gaussian.Physical.Fermion
