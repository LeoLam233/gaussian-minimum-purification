import Gaussian.Physical.Boson.CovarianceDomainBridge

/-! Raw finite pure covariance witnesses are realized by genuine four-party pure
Gaussian states with the prescribed full physical marginal and exact sidewise entropy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase WithLp
variable {A B C D : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

def physicalMeanExtension
    (m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ) :
    (FourConfiguration A B C D×FourConfiguration A B C D) →ₗ[ℝ] ℝ :=
  m.comp ((LinearMap.fst ℝ (JointConfiguration A B×JointConfiguration A B)
      (JointConfiguration C D×JointConfiguration C D)).comp
        (phaseProductEquiv (JointConfiguration A B) (JointConfiguration C D)).toLinearMap)

@[simp] theorem physicalMeanExtension_left
    (m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ)
    (z : JointConfiguration A B×JointConfiguration A B) :
    physicalMeanExtension (C := C) (D := D) m (leftPhaseEmbedding z)=m z := by
  change m (phaseProductEquiv (JointConfiguration A B) (JointConfiguration C D) (leftPhaseEmbedding z)).1=m z
  rw [phaseProductEquiv_left]

lemma pureCovarianceProductConfiguration_cost
    (d : PureCompatibleCovariance (productForm (weylSymplecticForm (JointConfiguration A B))
      (weylSymplecticForm (JointConfiguration C D)))) :
    (pureCovarianceProductCoordinates (pureCovarianceConfigurationCoordinates d)).auxiliaryCutCost
      (physicalPhaseSubspace A B) (physicalPhaseSubspace C D)=
        d.auxiliaryCutCost (physicalPhaseSubspace A B) (physicalPhaseSubspace C D) := by
  unfold PureCompatibleCovariance.auxiliaryCutCost
  apply bosonFormCost_congr_forms
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (pureCovarianceProductCoordinates (pureCovarianceConfigurationCoordinates d)).form
      (x.1,x.2) (y.1,y.2)=d.form (x.1,x.2) (y.1,y.2)
    rw [pureCovarianceProductCoordinates_form,pureCovarianceConfigurationCoordinates_form,
      LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  · rfl

/-- The physical mean is extended linearly and the true partial trace is identified
with the prescribed density by the proved full Weyl-characteristic uniqueness. -/
theorem exists_sidewisePurifier_of_covariance
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V)
    (d : PureCompatibleCovariance (productForm (weylSymplecticForm (JointConfiguration A B))
      (weylSymplecticForm (JointConfiguration C D))))
    (hphysical : ∀ x y, d.form (x,0) (y,0)=V x y) :
    ∃ σ : NormalDensity (Schrodinger (FourConfiguration A B C D)),
      IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
      (sidewiseEntropy σ).toReal=d.auxiliaryCutCost (physicalPhaseSubspace A B) (physicalPhaseSubspace C D) := by
  let d' := pureCovarianceConfigurationCoordinates d
  obtain ⟨σ,hσ,hpure,he⟩ := exists_pure_gaussian_of_compatible d'
    (physicalMeanExtension (C := C) (D := D) m)
  have hm : (physicalMeanExtension (C := C) (D := D) m).comp leftPhaseEmbedding=m := by
    apply LinearMap.ext
    exact physicalMeanExtension_left m
  have hv : d'.form.compl₁₂ leftPhaseEmbedding leftPhaseEmbedding=V := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change d'.form (leftPhaseEmbedding x) (leftPhaseEmbedding y)=V x y
    rw [pureCovarianceConfigurationCoordinates_form,phaseProductEquiv_left,phaseProductEquiv_left]
    exact hphysical x y
  have hred : IsGaussianWith σ.leftReduction m V := by
    simpa only [hm,hv] using hσ.leftReduction
  have hent := hσ.sidewiseReduction.entropy_objective
    (Module.finBasis ℝ (JointConfiguration A C×JointConfiguration A C))
  refine ⟨σ,⟨⟨hpure,⟨_,_,hσ⟩⟩,hred.density_unique hρ⟩,hent.1,?_⟩
  change (sidewiseReduction σ).entropy.toReal=_
  rw [hent.2,← pureCovariance_sidewise_cost A B C D d',pureCovarianceProductConfiguration_cost]

lemma phaseProductEquiv_map_physicalPhaseSubspace :
    (physicalPhaseSubspace C D).map (phaseProductEquiv C D).toLinearMap=
      (LinearMap.inl ℝ (C×C) (D×D)).range := by
  change (leftPhaseEmbedding (E := C) (F := D)).range.map (phaseProductEquiv C D).toLinearMap=_
  rw [← LinearMap.range_comp]
  congr 1

/-- Canonical sidewise raw witnesses, including unequal or zero sides, are actual
purifiers with exactly the prescribed physical density and objective. -/
theorem exists_sidewisePurifier_of_canonical_covariance
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V)
    (d : PureCompatibleCovariance (productForm (weylSymplecticForm (JointConfiguration A B))
      (productForm (weylSymplecticForm C) (weylSymplecticForm D))))
    (hphysical : ∀ x y, d.form (x,0) (y,0)=V x y) :
    ∃ σ : NormalDensity (Schrodinger (FourConfiguration A B C D)),
      IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
      (sidewiseEntropy σ).toReal=d.auxiliaryCutCost (physicalPhaseSubspace A B)
        (LinearMap.inl ℝ (C×C) (D×D)).range := by
  let d' := d.pullbackAuxiliary (phaseProductEquiv C D) (phaseProductEquiv_weylForm C D)
  obtain ⟨σ,hσ,hfin,he⟩ := exists_sidewisePurifier_of_covariance hρ d' (by
    intro x y
    rw [PureCompatibleCovariance.pullbackAuxiliary_physical]
    exact hphysical x y)
  refine ⟨σ,hσ,hfin,he.trans ?_⟩
  rw [PureCompatibleCovariance.auxiliaryCutCost_pullbackAuxiliary _ _ _ _ _
    (physicalPhaseSubspace_nondegenerate A B) (physicalPhaseSubspace_nondegenerate C D),
    phaseProductEquiv_map_physicalPhaseSubspace]

end Gaussian.Physical.Boson
