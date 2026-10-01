import Gaussian.Physical.Fermion.OrthogonalSpectrum

noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

@[simp] theorem coefficientMatrix_entry {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) (a b : MajoranaIndex n) :
    coefficientMatrix R a b = R (coefficientBasis n b) a := by
  have h := congrArg (fun L : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n =>
    L (coefficientBasis n b) a) (coefficientMatrix_toEuclidean R)
  change (∑ j,coefficientMatrix R a j * (coefficientBasis n b) j) =
    R (coefficientBasis n b) a at h
  simpa only [coefficientBasis,PiLp.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h

theorem coefficientMatrix_transpose_mul {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    (coefficientMatrix R)ᵀ * coefficientMatrix R = 1 := by
  ext a b
  have h := R.inner_map_map (coefficientBasis n b) (coefficientBasis n a)
  change (∑ i,R (coefficientBasis n a) i * R (coefficientBasis n b) i) = _ at h
  simpa [Matrix.mul_apply,Matrix.transpose_apply,coefficientMatrix_entry,
    coefficientBasis,PiLp.single_apply,Matrix.one_apply,EuclideanSpace.inner_single_left,eq_comm] using h

@[simp] theorem coefficientMatrix_transpose {n : ℕ}
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    (coefficientMatrix R)ᵀ = coefficientMatrix R⁻¹ := by
  calc
    (coefficientMatrix R)ᵀ = (coefficientMatrix R)ᵀ *
      (coefficientMatrix R * coefficientMatrix R⁻¹) := by simp
    _ = ((coefficientMatrix R)ᵀ * coefficientMatrix R) * coefficientMatrix R⁻¹ := by
      rw [Matrix.mul_assoc]
    _ = coefficientMatrix R⁻¹ := by rw [coefficientMatrix_transpose_mul,Matrix.one_mul]

theorem implemented_generatorMatrix_conjugate {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    generatorMatrix (ρ.uConj U) = coefficientMatrix R * generatorMatrix ρ * coefficientMatrix R⁻¹ := by
  calc
    generatorMatrix (ρ.uConj U) = generatorMatrix (ρ.uConj U) *
      (coefficientMatrix R * coefficientMatrix R⁻¹) := by simp
    _ = (generatorMatrix (ρ.uConj U) * coefficientMatrix R) * coefficientMatrix R⁻¹ := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [implemented_generatorMatrix_intertwine ρ R U hU]

end Gaussian.Physical.Fermion
