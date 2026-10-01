import Gaussian.Physical.Boson.GaussianNormalForm
import Gaussian.Phase.BosonicPurificationCostTransport

/-! The actual extended von Neumann entropy and the independently defined finite
covariance objective agree, with finiteness and admissibility proved explicitly. -/
noncomputable section
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Raw symmetric uncertainty is exactly the realizable Gaussian covariance domain,
for every prescribed finite Weyl mean. The normal density is uniquely determined. -/
theorem existsUnique_gaussian_iff (m : (E×E) →ₗ[ℝ] ℝ) (V : LinearMap.BilinForm ℝ (E×E)) :
    (∃! ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ m V) ↔
      V.IsSymm ∧ Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E) := by
  constructor
  · rintro ⟨ρ,hρ,hu⟩
    exact ⟨hρ.1,hρ.uncertainty⟩
  · rintro ⟨hV,hunc⟩
    obtain ⟨ρ,hρ,he⟩ := exists_gaussian_with_entropy
      (phaseBasis (stdOrthonormalBasis ℝ E).toBasis) V hV hunc m
    exact ⟨ρ,hρ,fun σ hσ => hσ.density_unique hρ⟩

/-- The real objective is taken only after the actual entropy has been proved finite. -/
theorem IsGaussianWith.entropy_objective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.entropy≠⊤ ∧ ρ.entropy.toReal=
      bosonFormCost e V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt := by
  refine ⟨hρ.entropy_ne_top,?_⟩
  rw [hρ.entropy_eq_bosonFormCost e,ENNReal.toReal_ofReal]
  exact bosonFormCost_nonneg V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt
    weylSymplecticForm_nondegenerate hρ.uncertainty e

theorem IsGaussianWith.isPure_iff_bosonFormCost_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.IsPure ↔ bosonFormCost e V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt=0 := by
  rw [hρ.isPure_iff_entropy_eq_zero,hρ.entropy_eq_bosonFormCost e]
  constructor
  · intro h
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp h)
      (bosonFormCost_nonneg V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt
        weylSymplecticForm_nondegenerate hρ.uncertainty e)
  · intro h
    rw [h,ENNReal.ofReal_zero]

end Gaussian.Physical.Boson
