import Gaussian.Physical.Boson.GaussianNormalForm
import Gaussian.Phase.BosonicPurificationPadding

/-! Genuine rank-one normal Gaussian realization of every raw pure compatible
covariance, with arbitrary Weyl means and no bound on finite squeezing. -/
noncomputable section
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem IsGaussianWith.isPure_of_compatible
    (d : PureCompatibleCovariance (weylSymplecticForm E))
    {ρ : NormalDensity (Schrodinger E)} {m : (E×E) →ₗ[ℝ] ℝ}
    (hρ : IsGaussianWith ρ m d.form) : ρ.IsPure := by
  apply hρ.isPure_iff_entropy_eq_zero.mpr
  rw [hρ.entropy_eq_bosonFormCost (phaseBasis (stdOrthonormalBasis ℝ E).toBasis),
    d.formCost_eq_zero,ENNReal.ofReal_zero]

/-- The supplied object has only raw bilinear covariance/generator fields;
normal density, Gaussianity and true purity are all constructed conclusions. -/
theorem exists_pure_gaussian_of_compatible
    (d : PureCompatibleCovariance (weylSymplecticForm E)) (m : (E×E) →ₗ[ℝ] ℝ) :
    ∃ ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ m d.form ∧ ρ.IsPure ∧ ρ.entropy=0 := by
  obtain ⟨ρ,hρ,he⟩ := exists_gaussian_with_entropy
    (phaseBasis (stdOrthonormalBasis ℝ E).toBasis) d.form d.symmetric d.uncertainty m
  have hp := hρ.isPure_of_compatible d
  exact ⟨ρ,hρ,hp,hp.entropy_eq_zero⟩

end Gaussian.Physical.Boson
