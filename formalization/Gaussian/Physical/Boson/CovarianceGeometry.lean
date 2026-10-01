import Gaussian.Physical.Boson.WeylUncertainty
import Gaussian.Phase.BosonicPurification

/-! Physical Gaussian input supplies the raw finite-dimensional geometry.
The doubled output below is a covariance; actual normal-state purification
and the entropy bridge are deliberately separate conclusions. -/
noncomputable section
namespace Gaussian.Physical.Boson
open Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Adaptation follows from the actual Weyl state, without an uncertainty or
strict-positivity premise supplied by the caller. -/
theorem IsGaussianWith.exists_adapted_geometry {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (h : IsGaussianWith ρ m V) :
    ∃ d : BosonicAdaptationData V (weylSymplecticForm E), ∀ z, d.g z z ≤ V z z := by
  exact Gaussian.Covariance.exists_bosonicAdaptation_from_uncertainty
    V (weylSymplecticForm E) h.1 weylSymplecticForm_isAlt
    weylSymplecticForm_nondegenerate
    (even_finrank_of_nondegenerate_alternating _ weylSymplecticForm_isAlt
      weylSymplecticForm_nondegenerate) h.uncertainty

/-- Every actual finite-mode normal Gaussian input has an explicit admissible
same-sign doubled pure covariance with its exact physical restriction. -/
theorem IsGaussianWith.exists_reference_covariance {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (h : IsGaussianWith ρ m V) :
    ∃ p : PureCompatibleCovariance (doubledForm (weylSymplecticForm E) (weylSymplecticForm E)),
      (∀ x y, p.form (x,0) (y,0)=V x y) ∧
      Gaussian.Covariance.RealifiedUncertainty p.form
        (doubledForm (weylSymplecticForm E) (weylSymplecticForm E)) := by
  exact exists_bosonic_reference_compatible V (weylSymplecticForm E) h.1
    weylSymplecticForm_isAlt weylSymplecticForm_nondegenerate h.uncertainty

end Gaussian.Physical.Boson
