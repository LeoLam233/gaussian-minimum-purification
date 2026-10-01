import Gaussian.Physical.Boson.PhaseCoordinates
import Gaussian.Covariance.Uncertainty
import Gaussian.Spectral.WilliamsonCoefficients

/-! Raw Williamson coefficients in the actual Schrödinger q/p orientation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The raw uncertainty condition supplies a genuine paired basis with every physical mode,
including the empty phase space. No spectral or state-realization data is an input. -/
theorem exists_williamson_phase_basis (V : LinearMap.BilinForm ℝ (E×E))
    (hV : V.IsSymm) (hunc : Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E)) :
    ∃ (ν : Fin (finrank ℝ E) → ℝ) (b : Basis (Fin (finrank ℝ E) × Bool) ℝ (E×E)),
      (∀ i, 1 ≤ ν i) ∧
      (∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0) ∧
      (∀ i j, weylSymplecticForm E (b i) (b j) =
        if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
          else (if j.2 then 1 else 0)) else 0) := by
  classical
  have hn : finrank ℝ (E×E)=2*finrank ℝ E := by rw [Module.finrank_prod]; omega
  obtain ⟨ν,b,hν,hΩ,hbV⟩ := exists_williamson_basis_bool V (weylSymplecticForm E) hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hunc
      weylSymplecticForm_nondegenerate hx)
    weylSymplecticForm_isAlt weylSymplecticForm_nondegenerate hn
    (Gaussian.Covariance.robertson_inequality hunc)
  exact ⟨ν,b,hν,hbV,hΩ⟩

end Gaussian.Physical.Boson
