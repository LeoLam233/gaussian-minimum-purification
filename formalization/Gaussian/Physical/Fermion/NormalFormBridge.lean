import Gaussian.Physical.Fermion.ThermalGaussian

/-! Actual-state consequences of a separately proved covariance normal form.
These transport lemmas do not postulate a normal form, an entropy identity, or
Gaussian realizability as a structure field.  The geometric normal-form identity
must be proved at each final use. -/
noncomputable section
open scoped BigOperators
namespace Gaussian.Physical.Fermion

/-- Every orthogonal canonical covariance has a constructed actual quasifree
realization with the proved density-spectrum entropy. -/
theorem exists_orthogonal_thermal_state (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    ∃ ρ : Density n, IsQuasifree ρ ∧
      Sᵥₙ ρ = ∑ i, Gaussian.Entropy.fermion (t i) ∧
      ∀ a b, covariance ρ a b = covarianceForm (thermal n t ht)
        (R⁻¹ (coefficientBasis n a)) (R⁻¹ (coefficientBasis n b)) := by
  obtain ⟨U,hU⟩ := orthogonal_implemented n R
  refine ⟨(thermal n t ht).uConj U,rotated_thermal_isQuasifree n t ht R U hU,?_,?_⟩
  · rw [unitaryState_entropy,entropy_thermal]
  · intro a b
    rw [← covarianceForm_basis,implemented_covarianceForm _ R U hU]

/-- Matching actual covariance identifies an arbitrary input Wick density with
the constructed canonical orthogonal image, by proved CAR moment uniqueness. -/
theorem quasifree_eq_rotated_thermal_of_covariance (n : ℕ) (ρ : Density n)
    (hρ : IsQuasifree ρ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U)
    (hΓ : ∀ a b, covariance ρ a b = covarianceForm (thermal n t ht)
      (R⁻¹ (coefficientBasis n a)) (R⁻¹ (coefficientBasis n b))) :
    ρ = (thermal n t ht).uConj U := by
  apply quasifree_eq_of_covariance ρ _ hρ (rotated_thermal_isQuasifree n t ht R U hU)
  intro a b
  rw [hΓ,← covarianceForm_basis,implemented_covarianceForm _ R U hU]

/-- Actual input von Neumann entropy follows from an explicit covariance normal-form identity. -/
theorem quasifree_entropy_of_covariance_normal_form (n : ℕ) (ρ : Density n)
    (hρ : IsQuasifree ρ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (hΓ : ∀ a b, covariance ρ a b = covarianceForm (thermal n t ht)
      (R⁻¹ (coefficientBasis n a)) (R⁻¹ (coefficientBasis n b))) :
    Sᵥₙ ρ = ∑ i, Gaussian.Entropy.fermion (t i) := by
  obtain ⟨U,hU⟩ := orthogonal_implemented n R
  rw [quasifree_eq_rotated_thermal_of_covariance n ρ hρ t ht R U hU hΓ,
    unitaryState_entropy,entropy_thermal]

end Gaussian.Physical.Fermion
