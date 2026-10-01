import Gaussian.Physical.Fermion.CovariancePositivity

/-! Explicit sign bridge between trace covariance entries and the left-slot
real skew generator used by the geometric adaptation. -/
noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- Left-slot generator: ⟪T v,w⟫=vᵀΓw, hence its column matrix is −Γ. -/
def covarianceGenerator {n : ℕ} (ρ : Density n) : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n :=
  Matrix.toEuclideanLin (fun a b => -covariance ρ a b)

theorem covarianceGenerator_inner {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    ⟪covarianceGenerator ρ v,w⟫ = covarianceForm ρ v w := by
  rw [covarianceForm_matrix]
  change (∑ a, w a * (∑ b, -covariance ρ a b * v b)) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [covariance_skew ρ b a]
  ring

theorem covarianceForm_skew {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    covarianceForm ρ v w = -covarianceForm ρ w v := by
  rw [covarianceForm_matrix,covarianceForm_matrix,Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [covariance_skew ρ b a]
  ring

theorem covarianceGenerator_skew {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    ⟪covarianceGenerator ρ v,w⟫ = -⟪v,covarianceGenerator ρ w⟫ := by
  calc
    ⟪covarianceGenerator ρ v,w⟫ = covarianceForm ρ v w := covarianceGenerator_inner ρ v w
    _ = -covarianceForm ρ w v := covarianceForm_skew ρ v w
    _ = -⟪v,covarianceGenerator ρ w⟫ := by
      rw [← covarianceGenerator_inner ρ w v]
      exact congrArg Neg.neg (real_inner_comm _ _)

/-- The actual iΓ covariance is Hermitian, proved from its real skew entries. -/
theorem hermitianCovariance_isHermitian {n : ℕ} (ρ : Density n) :
    (hermitianCovariance ρ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply,hermitianCovariance,star_mul,
    Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  rw [covariance_skew ρ b a]
  simp [mul_comm]

/-- Bundled actual Hermitian covariance for the spectral entropy API. -/
def covarianceHermitianMat {n : ℕ} (ρ : Density n) : HermitianMat (MajoranaIndex n) ℂ :=
  ⟨hermitianCovariance ρ,hermitianCovariance_isHermitian ρ⟩

end Gaussian.Physical.Fermion
