import Gaussian.Physical.Fermion.CovarianceOperator
import Gaussian.Spectral.Complexification

noncomputable section
open Module Gaussian.Spectral
open scoped Matrix
namespace Gaussian.Physical.Fermion

/-- The actual real coefficient matrix of an orthogonal transformation. -/
def coefficientMatrix {n : ℕ} (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.toEuclideanLin.symm R.toLinearEquiv.toLinearMap

@[simp] theorem coefficientMatrix_toEuclidean {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    Matrix.toEuclideanLin (coefficientMatrix R) = R.toLinearEquiv.toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

@[simp] theorem coefficientMatrix_one (n : ℕ) :
    coefficientMatrix (1 : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [coefficientMatrix_toEuclidean,Matrix.toLpLin_one]
  rfl

@[simp] theorem coefficientMatrix_mul {n : ℕ}
    (R S : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    coefficientMatrix (R*S) = coefficientMatrix R * coefficientMatrix S := by
  apply Matrix.toEuclideanLin.injective
  rw [coefficientMatrix_toEuclidean,Matrix.toLpLin_mul_same,
    coefficientMatrix_toEuclidean,coefficientMatrix_toEuclidean]
  ext v
  rfl

@[simp] theorem coefficientMatrix_mul_inverse {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    coefficientMatrix R * coefficientMatrix R⁻¹ = 1 := by
  rw [← coefficientMatrix_mul,mul_inv_cancel,coefficientMatrix_one]

@[simp] theorem coefficientMatrix_inverse_mul {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    coefficientMatrix R⁻¹ * coefficientMatrix R = 1 := by
  rw [← coefficientMatrix_mul,inv_mul_cancel,coefficientMatrix_one]

/-- Complexification of the actual orthogonal coefficient transformation. -/
def complexCoefficientEquiv {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    (MajoranaIndex n → ℂ) ≃ₗ[ℂ] (MajoranaIndex n → ℂ) :=
  complexifyLinearEquiv (coefficientMatrix R) (coefficientMatrix R⁻¹)
    (coefficientMatrix_mul_inverse R) (coefficientMatrix_inverse_mul R)

@[simp] theorem complexCoefficientEquiv_apply {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) (v : MajoranaIndex n → ℂ) :
    complexCoefficientEquiv R v = complexifyMatrix (coefficientMatrix R) *ᵥ v := rfl

end Gaussian.Physical.Fermion
