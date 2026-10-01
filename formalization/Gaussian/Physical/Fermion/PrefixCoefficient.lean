import Gaussian.Physical.Fermion.PrefixCoefficientBasis
import Gaussian.Physical.Fermion.CovarianceOperator

set_option autoImplicit false
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def actualCovarianceBilin {n : ℕ} (ρ : Density n) : LinearMap.BilinForm ℝ (CoefficientSpace n) :=
  (innerₗ (CoefficientSpace n)).comp (covarianceGenerator ρ)

@[simp] theorem actualCovarianceBilin_apply {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    actualCovarianceBilin ρ v w = covarianceForm ρ v w := covarianceGenerator_inner ρ v w

theorem prefixRestriction_covarianceBilin (k l : ℕ) (ρ : Density (l+k)) :
    actualCovarianceBilin (prefixRestriction k l ρ) =
      (actualCovarianceBilin ρ).compl₁₂ (prefixCoefficientEmbedding k l).toLinearMap
        (prefixCoefficientEmbedding k l).toLinearMap := by
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (MajoranaIndex k) ℝ).toBasis
  intro a b
  simp only [LinearMap.compl₁₂_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply,LinearIsometry.coe_toLinearMap,
    prefixCoefficientEmbedding_basis,actualCovarianceBilin_apply,covarianceForm_basis]
  exact prefixRestriction_covariance k l ρ a b

theorem prefixRestriction_covarianceForm (k l : ℕ) (ρ : Density (l+k))
    (v w : CoefficientSpace k) :
    covarianceForm (prefixRestriction k l ρ) v w =
      covarianceForm ρ (prefixCoefficientEmbedding k l v) (prefixCoefficientEmbedding k l w) := by
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (CoefficientSpace k) => B v w)
    (prefixRestriction_covarianceBilin k l ρ)
  simpa only [LinearMap.compl₁₂_apply,
    LinearIsometry.coe_toLinearMap,actualCovarianceBilin_apply] using h

/-- Physical partial trace after an actual implemented orthogonal transformation
restricts precisely the original trace-defined covariance to the selected rows. -/
theorem orthogonalRestriction_covarianceForm (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (v w : CoefficientSpace k) :
    covarianceForm (prefixRestriction k l (ρ.uConj U)) v w =
      covarianceForm ρ (R⁻¹ (prefixCoefficientEmbedding k l v))
        (R⁻¹ (prefixCoefficientEmbedding k l w)) := by
  rw [prefixRestriction_covarianceForm,implemented_covarianceForm _ R U hU]

end Gaussian.Physical.Fermion
