import Gaussian.Physical.Boson.WeylInjectivity
import Gaussian.Physical.Boson.ThermalCharacteristic
import Gaussian.Physical.Boson.MeanRemoval
import Gaussian.Physical.Boson.PureEntropy
import Gaussian.Physical.Boson.WeylUncertainty

/-! Actual Gaussian density uniqueness and canonical one-mode entropy classification.
These conclusions apply to the raw Weyl Gaussian predicate, rather than a thermal-orbit definition. -/
noncomputable section
namespace Gaussian.Physical.Boson
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The symmetric covariance and linear Weyl mean uniquely determine the actual normal density. -/
theorem IsGaussianWith.density_unique {ρ σ : NormalDensity (Schrodinger E)}
    {m : (E × E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E × E)}
    (hρ : IsGaussianWith ρ m V) (hσ : IsGaussianWith σ m V) : ρ = σ := by
  apply NormalDensity.ext_characteristic
  intro q p
  exact (hρ.2 q p).trans (hσ.2 q p).symm

/-- Every centered one-mode Gaussian with diagonal canonical covariance is the actual thermal density. -/
theorem IsGaussianWith.eq_schrodingerThermalDensity
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν)
    {ρ : NormalDensity (Schrodinger ℝ)}
    (hρ : IsGaussianWith ρ 0 (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2))) :
    ρ = schrodingerThermalDensity Q (thermalRatio ν) (thermalRatio_mem hν) :=
  hρ.density_unique (schrodingerThermalDensity_gaussian_entropy Q ν hν).1

/-- Actual CFC entropy of any raw Gaussian with canonical one-mode covariance, including arbitrary means. -/
theorem IsGaussianWith.entropy_eq_boson_one_mode
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν)
    {ρ : NormalDensity (Schrodinger ℝ)} {m : (ℝ × ℝ) →ₗ[ℝ] ℝ}
    (hρ : IsGaussianWith ρ m (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2))) :
    ρ.entropy = ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  obtain ⟨a,b,hc,he⟩ := hρ.exists_centered_displacement
  rw [← he, hc.eq_schrodingerThermalDensity Q ν hν]
  exact schrodingerThermalDensity_entropy_eq_boson Q hν

/-- The independently constructed Cartesian Gaussian noise mixture is the same actual thermal state. -/
theorem isotropicGaussianDensity_eq_thermal
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν) :
    isotropicGaussianDensity Q ν hν =
      schrodingerThermalDensity Q (thermalRatio ν) (thermalRatio_mem hν) :=
  (isotropicGaussianDensity_isGaussian Q ν hν).eq_schrodingerThermalDensity Q ν hν

/-- Canonical one-mode purity is derived from the actual normal density and its spectrum. -/
theorem IsGaussianWith.isPure_iff_one_mode
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν)
    {ρ : NormalDensity (Schrodinger ℝ)} {m : (ℝ × ℝ) →ₗ[ℝ] ℝ}
    (hρ : IsGaussianWith ρ m (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2))) :
    ρ.IsPure ↔ ν = 1 := by
  constructor
  · intro hp
    have he : ENNReal.ofReal (Gaussian.Entropy.boson ν) = 0 := by
      rw [← hρ.entropy_eq_boson_one_mode Q ν hν, hp.entropy_eq_zero]
    exact (Gaussian.Entropy.boson_eq_zero_iff hν).mp
      (le_antisymm (ENNReal.ofReal_eq_zero.mp he) (Gaussian.Entropy.boson_nonneg hν))
  · intro h
    subst ν
    let x := oscillatorBasis Q 0
    have hx : ‖x‖ = 1 := (oscillatorBasis Q).orthonormal.norm_eq_one 0
    have hg : IsGaussianWith (vectorDensity x hx) 0
        (diagonalCovariance (1/Q.ξ^2) (1*Q.ξ^2)) := by
      have hh := (schrodingerThermalDensity_gaussian_entropy Q 1 (by norm_num)).1
      have hr : thermalRatio 1 = 0 := by norm_num [thermalRatio]
      simpa only [hr, schrodingerThermalDensity_zero] using hh
    obtain ⟨a,b,hd,_⟩ := hg.exists_prescribed_mean m
    rw [hρ.density_unique hd]
    exact (show (vectorDensity x hx).IsPure from ⟨x,hx,rfl⟩).displace a b

/-- Every finite canonical covariance and every finite linear mean are realized by a normal state. -/
theorem exists_one_mode_gaussian_entropy
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν)
    (m : (ℝ × ℝ) →ₗ[ℝ] ℝ) :
    ∃ ρ : NormalDensity (Schrodinger ℝ),
      IsGaussianWith ρ m (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2)) ∧
      ρ.entropy = ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  obtain ⟨a,b,hg,he⟩ := (schrodingerThermalDensity_gaussian_entropy Q ν hν).1.exists_prescribed_mean m
  exact ⟨_,hg,he.trans (schrodingerThermalDensity_entropy_eq_boson Q hν)⟩

/-- Admissibility of the canonical parameter follows from actual state positivity. -/
theorem IsGaussianWith.one_le_one_mode_parameter
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ)
    {ρ : NormalDensity (Schrodinger ℝ)} {m : (ℝ × ℝ) →ₗ[ℝ] ℝ}
    (hρ : IsGaussianWith ρ m (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2))) : 1 ≤ ν := by
  have hs : Q.ξ ≠ 0 := Q.ξ_pos.ne'
  have h := hρ.uncertainty (Q.ξ,0) (0,1/Q.ξ)
  have h1 : diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2) (Q.ξ,0) (Q.ξ,0) = ν := by
    simp only [diagonalCovariance_apply, mul_zero, add_zero]
    field_simp
  have h2 : diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2) (0,1/Q.ξ) (0,1/Q.ξ) = ν := by
    simp only [diagonalCovariance_apply, mul_zero, zero_add]
    field_simp
  have h3 : weylSymplecticForm ℝ (Q.ξ,0) (0,1/Q.ξ) = 1 := by
    simp [weylSymplecticForm_apply, inner, hs]
  rw [h1,h2,h3] at h
  linarith

/-- No separate uncertainty or parameter-domain premise is needed for this entropy classification. -/
theorem IsGaussianWith.entropy_eq_boson_one_mode_raw
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ)
    {ρ : NormalDensity (Schrodinger ℝ)} {m : (ℝ × ℝ) →ₗ[ℝ] ℝ}
    (hρ : IsGaussianWith ρ m (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2))) :
    ρ.entropy = ENNReal.ofReal (Gaussian.Entropy.boson ν) :=
  hρ.entropy_eq_boson_one_mode Q ν (hρ.one_le_one_mode_parameter Q ν)

end Gaussian.Physical.Boson
