import Gaussian.Physical.Boson.GaussianState
import Gaussian.Physical.Boson.FourPartyConfiguration

/-! Actual four-party bosonic purification and entropy objective. The marginal
and cut are genuine normal-density partial traces after an actual configuration
unitary. No covariance spectrum or optimization conclusion is a domain field. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open WithLp
variable {A B C D : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

abbrev FourConfiguration (A B C D : Type*) :=
  JointConfiguration (JointConfiguration A B) (JointConfiguration C D)

def sidewiseReduction (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) :
    NormalDensity (Schrodinger (JointConfiguration A C)) :=
  (σ.mapConfiguration (fourPartyReorder A B C D)).leftReduction

def sidewiseEntropy (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) : ENNReal :=
  (sidewiseReduction σ).entropy

def IsSidewisePurifier (ρ : NormalDensity (Schrodinger (JointConfiguration A B)))
    (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) : Prop :=
  IsPureGaussian σ ∧ σ.leftReduction=ρ

def sidewisePhaseEmbedding :
    (JointConfiguration A C×JointConfiguration A C) →ₗ[ℝ]
      (FourConfiguration A B C D×FourConfiguration A B C D) :=
  ((fourPartyReorder A B C D).symm.toLinearEquiv.prodCongr
    (fourPartyReorder A B C D).symm.toLinearEquiv).toLinearMap.comp
      (leftPhaseEmbedding (E := JointConfiguration A C) (F := JointConfiguration B D))

theorem sidewiseReduction_characteristic
    (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) (q p : JointConfiguration A C) :
    (sidewiseReduction σ).characteristic q p=
      σ.characteristic (sidewisePhaseEmbedding (B := B) (D := D) (q,p)).1
        (sidewisePhaseEmbedding (B := B) (D := D) (q,p)).2 := by
  unfold sidewiseReduction
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_mapConfiguration]
  rfl

theorem IsGaussianWith.sidewiseReduction
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    {m : (FourConfiguration A B C D×FourConfiguration A B C D) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (FourConfiguration A B C D×FourConfiguration A B C D)}
    (hσ : IsGaussianWith σ m V) :
    IsGaussianWith (sidewiseReduction σ) (m.comp sidewisePhaseEmbedding)
      (V.compl₁₂ sidewisePhaseEmbedding sidewisePhaseEmbedding) := by
  refine ⟨⟨fun x y => hσ.1.eq _ _⟩,?_⟩
  intro q p
  rw [sidewiseReduction_characteristic,hσ.2]
  rfl

theorem IsSidewisePurifier.sidewise_isGaussian
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    (hσ : IsSidewisePurifier ρ σ) : IsGaussian (sidewiseReduction σ) := by
  obtain ⟨m,V,h⟩ := hσ.1.2
  exact ⟨_,_,h.sidewiseReduction⟩

end Gaussian.Physical.Boson
