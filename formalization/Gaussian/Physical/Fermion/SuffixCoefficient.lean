import Gaussian.Physical.Fermion.SuffixCoefficientBasis
import Gaussian.Physical.Fermion.PrefixCoefficient

set_option autoImplicit false
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem suffixRestriction_covarianceBilin (k l : ℕ) (ρ : Density (l+k)) :
    actualCovarianceBilin (suffixRestriction k l ρ) =
      (actualCovarianceBilin ρ).compl₁₂ (suffixCoefficientEmbedding k l).toLinearMap
        (suffixCoefficientEmbedding k l).toLinearMap := by
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (MajoranaIndex l) ℝ).toBasis
  intro a b
  simp only [LinearMap.compl₁₂_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply,LinearIsometry.coe_toLinearMap,
    suffixCoefficientEmbedding_basis,actualCovarianceBilin_apply,covarianceForm_basis]
  exact suffixRestriction_covariance k l ρ a b

theorem suffixRestriction_covarianceForm (k l : ℕ) (ρ : Density (l+k))
    (v w : CoefficientSpace l) :
    covarianceForm (suffixRestriction k l ρ) v w =
      covarianceForm ρ (suffixCoefficientEmbedding k l v) (suffixCoefficientEmbedding k l w) := by
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (CoefficientSpace l) => B v w)
    (suffixRestriction_covarianceBilin k l ρ)
  simpa only [LinearMap.compl₁₂_apply,
    LinearIsometry.coe_toLinearMap,actualCovarianceBilin_apply] using h

/-- Physical partial trace after an actual implemented orthogonal transformation
restricts precisely the original trace-defined covariance to the selected rows. -/
theorem orthogonalSuffixRestriction_covarianceForm (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (v w : CoefficientSpace l) :
    covarianceForm (suffixRestriction k l (ρ.uConj U)) v w =
      covarianceForm ρ (R⁻¹ (suffixCoefficientEmbedding k l v))
        (R⁻¹ (suffixCoefficientEmbedding k l w)) := by
  rw [suffixRestriction_covarianceForm,implemented_covarianceForm _ R U hU]

end Gaussian.Physical.Fermion
