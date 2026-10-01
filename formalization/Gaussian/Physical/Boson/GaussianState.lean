import Gaussian.Physical.Boson.LeftReduction
import Gaussian.Physical.Boson.ConfigurationDensityTransport

/-! Raw finite bosonic Gaussian and pure-Gaussian state predicates. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def IsGaussian (ρ : NormalDensity (Schrodinger E)) : Prop :=
  ∃ m V,IsGaussianWith ρ m V

def IsPureGaussian (ρ : NormalDensity (Schrodinger E)) : Prop := ρ.IsPure ∧ IsGaussian ρ

theorem IsGaussian.leftReduction {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    (hρ : IsGaussian ρ) : IsGaussian ρ.leftReduction := by
  obtain ⟨m,V,h⟩ := hρ
  exact ⟨_,_,h.leftReduction⟩

theorem IsGaussian.mapConfiguration {ρ : NormalDensity (Schrodinger E)}
    (hρ : IsGaussian ρ) (e : E ≃ₗᵢ[ℝ] F) : IsGaussian (ρ.mapConfiguration e) := by
  obtain ⟨m,V,h⟩ := hρ
  exact ⟨_,_,h.mapConfiguration e⟩

theorem IsPureGaussian.mapConfiguration {ρ : NormalDensity (Schrodinger E)}
    (hρ : IsPureGaussian ρ) (e : E ≃ₗᵢ[ℝ] F) : IsPureGaussian (ρ.mapConfiguration e) :=
  ⟨(ρ.mapConfiguration_isPure_iff e).mpr hρ.1,hρ.2.mapConfiguration e⟩

end Gaussian.Physical.Boson
