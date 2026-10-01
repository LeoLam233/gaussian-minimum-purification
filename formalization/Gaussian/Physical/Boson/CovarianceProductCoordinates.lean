import Gaussian.Physical.Boson.ProductPhaseCoordinates
import Gaussian.Physical.Boson.GaussianPurity

/-! Genuine pullback of pure compatible covariance between configuration phase
coordinates and the physical/auxiliary direct sum, preserving both raw forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem phaseProductEquiv_pullback_weylForm :
    (weylSymplecticForm (JointConfiguration E F)).compl₁₂
      (phaseProductEquiv E F).symm.toLinearMap (phaseProductEquiv E F).symm.toLinearMap=
        productForm (weylSymplecticForm E) (weylSymplecticForm F) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro w
  change weylSymplecticForm (JointConfiguration E F) ((phaseProductEquiv E F).symm z)
    ((phaseProductEquiv E F).symm w)=productForm (weylSymplecticForm E) (weylSymplecticForm F) z w
  have h := phaseProductEquiv_weylForm E F ((phaseProductEquiv E F).symm z) ((phaseProductEquiv E F).symm w)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

def pureCovarianceProductCoordinates
    (d : PureCompatibleCovariance (weylSymplecticForm (JointConfiguration E F))) :
    PureCompatibleCovariance (productForm (weylSymplecticForm E) (weylSymplecticForm F)) :=
  (d.pullback (phaseProductEquiv E F).symm).of_form_eq phaseProductEquiv_pullback_weylForm

@[simp] theorem pureCovarianceProductCoordinates_form
    (d : PureCompatibleCovariance (weylSymplecticForm (JointConfiguration E F)))
    (z w : (E×E)×(F×F)) :
    (pureCovarianceProductCoordinates d).form z w=
      d.form ((phaseProductEquiv E F).symm z) ((phaseProductEquiv E F).symm w) := by
  rw [pureCovarianceProductCoordinates,PureCompatibleCovariance.of_form_eq_form,
    PureCompatibleCovariance.pullback_form]

@[simp] theorem phaseProductEquiv_symm_left (z : E×E) :
    (phaseProductEquiv E F).symm (z,0)=leftPhaseEmbedding z := by
  apply (phaseProductEquiv E F).injective
  rw [LinearEquiv.apply_symm_apply,phaseProductEquiv_left]

@[simp] theorem pureCovarianceProductCoordinates_physical
    (d : PureCompatibleCovariance (weylSymplecticForm (JointConfiguration E F))) (z w : E×E) :
    (pureCovarianceProductCoordinates d).form (z,0) (w,0)=
      d.form (leftPhaseEmbedding z) (leftPhaseEmbedding w) := by
  rw [pureCovarianceProductCoordinates_form,phaseProductEquiv_symm_left,phaseProductEquiv_symm_left]

/-- The inverse coordinate direction is the same actual raw pullback. -/
def pureCovarianceConfigurationCoordinates
    (d : PureCompatibleCovariance (productForm (weylSymplecticForm E) (weylSymplecticForm F))) :
    PureCompatibleCovariance (weylSymplecticForm (JointConfiguration E F)) :=
  (d.pullback (phaseProductEquiv E F)).of_form_eq (by
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    exact phaseProductEquiv_weylForm E F z w)

@[simp] theorem pureCovarianceConfigurationCoordinates_form
    (d : PureCompatibleCovariance (productForm (weylSymplecticForm E) (weylSymplecticForm F)))
    (z w : JointConfiguration E F×JointConfiguration E F) :
    (pureCovarianceConfigurationCoordinates d).form z w=
      d.form (phaseProductEquiv E F z) (phaseProductEquiv E F w) := by
  rw [pureCovarianceConfigurationCoordinates,PureCompatibleCovariance.of_form_eq_form,
    PureCompatibleCovariance.pullback_form]

end Gaussian.Physical.Boson
