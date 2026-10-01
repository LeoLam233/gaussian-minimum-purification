import Gaussian.Physical.Boson.ConfigurationIsometry
import Gaussian.Physical.Boson.IsometryDensity
import Gaussian.Physical.Boson.GaussianPredicate

/-! Transport of actual normal densities across configuration-coordinate isometries. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def NormalDensity.mapConfiguration (ρ : NormalDensity (Schrodinger E)) (e : E ≃ₗᵢ[ℝ] F) :
    NormalDensity (Schrodinger F) := ρ.mapHilbert (schrodingerIsometry e)

theorem isometry_inverse_weyl (e : E ≃ₗᵢ[ℝ] F) (q p : F) :
    (schrodingerIsometry e).symm.conjStarAlgEquiv
      (weylOperator q p : Schrodinger F →L[ℂ] Schrodinger F)=
      (weylOperator (e.symm q) (e.symm p) : Schrodinger E →L[ℂ] Schrodinger E) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (schrodingerIsometry e).injective
  change _=schrodingerIsometry e (weyl (e.symm q) (e.symm p) f)
  rw [schrodingerIsometry_weyl]
  simp

theorem NormalDensity.characteristic_mapConfiguration
    (ρ : NormalDensity (Schrodinger E)) (e : E ≃ₗᵢ[ℝ] F) (q p : F) :
    (ρ.mapConfiguration e).characteristic q p=ρ.characteristic (e.symm q) (e.symm p) := by
  unfold NormalDensity.mapConfiguration NormalDensity.characteristic
  rw [NormalDensity.expect_mapHilbert,isometry_inverse_weyl]

theorem NormalDensity.mapConfiguration_isPure_iff
    (ρ : NormalDensity (Schrodinger E)) (e : E ≃ₗᵢ[ℝ] F) :
    (ρ.mapConfiguration e).IsPure ↔ ρ.IsPure :=
  ρ.mapHilbert_isPure_iff (schrodingerIsometry e)

theorem IsGaussianWith.mapConfiguration {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) (e : E ≃ₗᵢ[ℝ] F) :
    IsGaussianWith (ρ.mapConfiguration e)
      (m.comp (e.symm.toLinearEquiv.prodCongr e.symm.toLinearEquiv).toLinearMap)
      (V.compl₁₂ (e.symm.toLinearEquiv.prodCongr e.symm.toLinearEquiv).toLinearMap
        (e.symm.toLinearEquiv.prodCongr e.symm.toLinearEquiv).toLinearMap) := by
  refine ⟨⟨fun x y => hρ.1.eq _ _⟩,?_⟩
  intro q p
  rw [NormalDensity.characteristic_mapConfiguration,hρ.2]
  rfl

end Gaussian.Physical.Boson
