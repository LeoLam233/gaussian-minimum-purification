import Gaussian.Physical.Boson.Characteristic
import Gaussian.Physical.Boson.ThermalProductDensity
import Gaussian.Physical.Boson.NormalMixtureObservation
import Gaussian.Physical.Boson.ConfigurationIsometry
import Gaussian.Analysis.HilbertBasisTransport

/-! Actual Weyl transport for occupation-diagonal thermal states on transported complete bases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open Gaussian.Analysis
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem thermalProductDensity_map_characteristic {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ (Schrodinger E)) (e : E ≃ₗᵢ[ℝ] F)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) (q p : E) :
    (thermalProductDensity (mapHilbertBasis b (schrodingerIsometry e)) ν hν).characteristic (e q) (e p) =
      (thermalProductDensity b ν hν).characteristic q p := by
  let c := mapHilbertBasis b (schrodingerIsometry e)
  have hm : HasSum (fun k => (occupationThermalWeight ν k : ℂ)*⟪c k,weyl (e q) (e p) (c k)⟫_ℂ)
      ((thermalProductDensity c ν hν).characteristic (e q) (e p)) :=
    hasSum_normalMixture_expect _ (occupationThermalWeight_nonneg ν hν)
      (hasSum_occupationThermalWeight ν hν) c c.orthonormal.norm_eq_one (weylOperator (e q) (e p))
  have ho : HasSum (fun k => (occupationThermalWeight ν k : ℂ)*⟪b k,weyl q p (b k)⟫_ℂ)
      ((thermalProductDensity b ν hν).characteristic q p) :=
    hasSum_normalMixture_expect _ (occupationThermalWeight_nonneg ν hν)
      (hasSum_occupationThermalWeight ν hν) b b.orthonormal.norm_eq_one (weylOperator q p)
  have hi (k : Fin n → ℕ) : ⟪c k,weyl (e q) (e p) (c k)⟫_ℂ=⟪b k,weyl q p (b k)⟫_ℂ := by
    change ⟪mapHilbertBasis b (schrodingerIsometry e) k,
      weyl (e q) (e p) (mapHilbertBasis b (schrodingerIsometry e) k)⟫_ℂ=_
    rw [mapHilbertBasis_apply,← schrodingerIsometry_weyl,LinearIsometryEquiv.inner_map_map]
  simp_rw [hi] at hm
  exact hm.unique ho

end Gaussian.Physical.Boson
