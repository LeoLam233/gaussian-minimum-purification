import Gaussian.Phase.BosonicPurificationStandard
import Gaussian.Phase.BosonicPurificationPadding
import Mathlib.Algebra.Module.ULift

/-! Universe-independent standard auxiliary coefficient spaces. The lift is
an actual linear equivalence; it changes neither mode counts nor raw forms. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase

abbrev StandardBosonicSpaceLift (n : ℕ) : Type u := ULift.{u} (StandardBosonicSpace n)

def standardSymplecticFormLift (n : ℕ) : LinearMap.BilinForm ℝ (StandardBosonicSpaceLift.{u} n) :=
  (standardSymplecticForm (EuclideanSpace ℝ (Fin n))).compl₁₂
    (ULift.moduleEquiv.toLinearMap) (ULift.moduleEquiv.toLinearMap)

def standardPureCovarianceLift (n : ℕ) :
    PureCompatibleCovariance (standardSymplecticFormLift.{u} n) :=
  (standardPureCovariance (EuclideanSpace ℝ (Fin n))).pullback ULift.moduleEquiv

theorem finrank_standardBosonicSpaceLift (n : ℕ) :
    finrank ℝ (StandardBosonicSpaceLift.{u} n) = 2*n := by
  exact (ULift.moduleEquiv : StandardBosonicSpaceLift.{u} n ≃ₗ[ℝ] StandardBosonicSpace n).finrank_eq.trans
    (finrank_standardBosonicSpace n)

end Gaussian.Phase
