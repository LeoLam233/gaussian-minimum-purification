import Gaussian.Physical.Boson.ConfigurationDensityTransport
import Gaussian.Physical.Boson.ProductDensity
import Gaussian.Physical.Boson.RightPhaseEmbedding

/-! The actual right-factor partial trace, realized by the proved configuration
swap and the convergent left-factor partial trace. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def NormalDensity.rightReduction (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) :
    NormalDensity (Schrodinger F) :=
  (ρ.mapConfiguration (LinearIsometryEquiv.withLpProdComm 2 ℝ E F)).leftReduction

theorem NormalDensity.characteristic_rightReduction
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (q p : F) :
    ρ.rightReduction.characteristic q p=ρ.characteristic
      (rightConfigEmbedding (E := E) q) (rightConfigEmbedding (E := E) p) := by
  unfold NormalDensity.rightReduction
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_mapConfiguration]
  rfl

theorem IsGaussianWith.rightReduction
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V) :
    IsGaussianWith ρ.rightReduction (m.comp rightPhaseEmbedding)
      (V.compl₁₂ rightPhaseEmbedding rightPhaseEmbedding) := by
  refine ⟨⟨fun x y => hρ.1.eq _ _⟩,?_⟩
  intro q p
  rw [NormalDensity.characteristic_rightReduction,hρ.2]
  rfl

theorem NormalDensity.rightReduction_product (ρ : NormalDensity (Schrodinger E))
    (σ : NormalDensity (Schrodinger F)) : (ρ.product σ).rightReduction=σ := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_rightReduction,NormalDensity.characteristic_product]
  simp [rightConfigEmbedding_apply,NormalDensity.characteristic_zero]

theorem NormalDensity.eq_product_of_characteristic_factors
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F)))
    (hρ : ∀ q p,ρ.characteristic q p=
      ρ.leftReduction.characteristic (ofLp q).1 (ofLp p).1 *
      ρ.rightReduction.characteristic (ofLp q).2 (ofLp p).2) :
    ρ=ρ.leftReduction.product ρ.rightReduction := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_product,hρ]

end Gaussian.Physical.Boson
