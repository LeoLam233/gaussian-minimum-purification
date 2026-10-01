import Gaussian.Physical.Boson.CovarianceRealization

/-! Every arbitrary finite raw covariance purifier has an actual canonical
sidewise Gaussian realization with its exact two auxiliary counts and objective. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]

theorem covariancePurifier_exists_sidewise_realization
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V) {M : ℕ}
    (p : BosonicCovariancePurifier V (weylSymplecticForm (JointConfiguration A B)) M) :
    ∃ a b : ℕ, a+b=M ∧ a=p.leftModes ∧ b=p.rightModes ∧
      ∃ σ : NormalDensity (Schrodinger (FourConfiguration A B (CanonicalConfiguration a) (CanonicalConfiguration b))),
        IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
        (sidewiseEntropy σ).toReal=p.cost (physicalPhaseSubspace A B) := by
  obtain ⟨a,b,hab,ha,hb,d,hphysical,hcost⟩ := p.exists_canonical_sidewise_transport
    (physicalPhaseSubspace A B) (physicalPhaseSubspace_nondegenerate A B)
  obtain ⟨σ,hσ,hfin,he⟩ := exists_sidewisePurifier_of_canonical_covariance
    (C := CanonicalConfiguration a) (D := CanonicalConfiguration b) hρ d hphysical
  exact ⟨a,b,hab,ha,hb,σ,hσ,hfin,he.trans hcost⟩

end Gaussian.Physical.Boson
