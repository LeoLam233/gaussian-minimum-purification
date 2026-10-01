import Gaussian.Physical.Boson.CanonicalGaussian
import Gaussian.Physical.Boson.ThermalIsometry

/-! Concrete canonical Gaussian reference densities on any finite configuration carrier,
using a proved configuration isometry and an actual transported occupation basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Gaussian.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def canonicalPhaseCoordinates {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n) :
    (E×E) ≃ₗ[ℝ] (CanonicalConfiguration n × CanonicalConfiguration n) :=
  e.toLinearEquiv.prodCongr e.toLinearEquiv

def canonicalCovarianceOn {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n) (ν : Fin n → ℝ) :
    LinearMap.BilinForm ℝ (E×E) :=
  (canonicalCovariance ν).compl₁₂ (canonicalPhaseCoordinates e).toLinearMap
    (canonicalPhaseCoordinates e).toLinearMap

def canonicalThermalOn {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) : NormalDensity (Schrodinger E) :=
  thermalProductDensity (mapHilbertBasis (canonicalOscillatorBasis n) (schrodingerIsometry e.symm)) ν hν

theorem canonicalThermalOn_characteristic {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) (q p : E) :
    (canonicalThermalOn e ν hν).characteristic q p=(canonicalThermalDensity ν hν).characteristic (e q) (e p) := by
  simpa only [canonicalThermalOn,canonicalThermalDensity,e.symm_apply_apply] using thermalProductDensity_map_characteristic
    (canonicalOscillatorBasis n) e.symm ν hν (e q) (e p)

theorem canonicalThermalOn_isGaussian {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    IsGaussianWith (canonicalThermalOn e ν hν) 0 (canonicalCovarianceOn e ν) := by
  refine ⟨⟨fun x y => (canonicalCovariance_symm ν).eq (canonicalPhaseCoordinates e x)
    (canonicalPhaseCoordinates e y)⟩,?_⟩
  intro q p
  rw [canonicalThermalOn_characteristic,(canonicalThermalDensity_isGaussian ν hν).2]
  rfl

theorem canonicalThermalOn_entropy {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (canonicalThermalOn e ν hν).entropy=ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) :=
  thermalProductDensity_entropy _ ν hν

theorem canonicalThermalOn_isPure_iff {n : ℕ} (e : E ≃ₗᵢ[ℝ] CanonicalConfiguration n)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (canonicalThermalOn e ν hν).IsPure ↔ ∀ i, ν i=1 :=
  thermalProductDensity_isPure_iff _ ν hν

end Gaussian.Physical.Boson
