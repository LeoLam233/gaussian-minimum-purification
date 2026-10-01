import Gaussian.Physical.Boson.CovarianceCutCoordinates
import Gaussian.Physical.Boson.GaussianEntropyObjective
import Gaussian.Physical.Boson.GaussianParameters
import Gaussian.Phase.BosonicPurificationDomain

/-! Every actual finite four-party pure Gaussian competitor gives a raw covariance
purifier with exact physical covariance, both auxiliary counts, and the same AA′ cost. -/
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase WithLp
variable {A B C D : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem IsSidewisePurifier.exists_covariancePurifier
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V) (hσ : IsSidewisePurifier ρ σ) :
    ∃ p : BosonicCovariancePurifier V (weylSymplecticForm (JointConfiguration A B))
        (finrank ℝ C+finrank ℝ D),
      p.leftModes=finrank ℝ C ∧ p.rightModes=finrank ℝ D ∧
      sidewiseEntropy σ≠⊤ ∧ (sidewiseEntropy σ).toReal=p.cost (physicalPhaseSubspace A B) := by
  obtain ⟨mt,W,hW⟩ := hσ.1.2
  obtain ⟨d,hd⟩ := hW.exists_pureCompatible_of_isPure hσ.1.1
  have hr : IsGaussianWith ρ (mt.comp leftPhaseEmbedding)
      (W.compl₁₂ leftPhaseEmbedding leftPhaseEmbedding) := hσ.2 ▸ hW.leftReduction
  have hVeq := hr.covariance_unique hρ
  let q := pureCovarianceProductCoordinates d
  have hphysical (x y : JointConfiguration A B×JointConfiguration A B) :
      q.form (x,0) (y,0)=V x y := by
    rw [pureCovarianceProductCoordinates_physical,hd]
    exact congrArg (fun T : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B) => T x y) hVeq
  have hdim : finrank ℝ (JointConfiguration C D)=finrank ℝ C+finrank ℝ D := by
    rw [(WithLp.linearEquiv 2 ℝ (C×D)).finrank_eq,Module.finrank_prod]
  let p : BosonicCovariancePurifier V (weylSymplecticForm (JointConfiguration A B))
      (finrank ℝ C+finrank ℝ D) := {
    Auxiliary := JointConfiguration C D×JointConfiguration C D
    commutator := weylSymplecticForm (JointConfiguration C D)
    alternating := weylSymplecticForm_isAlt
    nondegenerate := weylSymplecticForm_nondegenerate
    mode_count := by rw [Module.finrank_prod,hdim]; omega
    covariance := q
    physical := hphysical
    split := physicalPhaseSubspace C D
    split_nondegenerate := physicalPhaseSubspace_nondegenerate C D }
  have hleft : p.leftModes=finrank ℝ C := by
    change finrank ℝ (physicalPhaseSubspace C D)/2=finrank ℝ C
    rw [physicalPhaseSubspace_finrank]
    omega
  have hright : p.rightModes=finrank ℝ D := by
    change finrank ℝ C+finrank ℝ D-p.leftModes=finrank ℝ D
    rw [hleft]
    omega
  have he := hW.sidewiseReduction.entropy_objective
    (Module.finBasis ℝ (JointConfiguration A C×JointConfiguration A C))
  refine ⟨p,hleft,hright,he.1,?_⟩
  change (sidewiseReduction σ).entropy.toReal=q.auxiliaryCutCost (physicalPhaseSubspace A B) (physicalPhaseSubspace C D)
  rw [he.2,pureCovariance_sidewise_cost]
  apply bosonFormCost_congr_forms
  · rw [hd]
  · rfl

end Gaussian.Physical.Boson
