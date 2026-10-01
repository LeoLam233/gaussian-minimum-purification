import Gaussian.Physical.Boson.CircularThermal

/-! The full one-mode thermal Weyl/entropy bridge, including the exact vacuum endpoint.
The operator is the actual infinite geometric oscillator density, not a covariance record. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped InnerProductSpace ENNReal

theorem schrodingerThermalDensity_zero
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (hr : (0:ℝ) ∈ Set.Ico 0 1) :
    schrodingerThermalDensity Q 0 hr =
      vectorDensity (oscillatorBasis Q 0) ((oscillatorBasis Q).orthonormal.norm_eq_one 0) := by
  apply NormalDensity.ext
  change (∑' n : ℕ, (thermalWeight 0 n : ℂ) • vectorOperator (oscillatorBasis Q n)) =
    vectorOperator (oscillatorBasis Q 0)
  rw [tsum_eq_single 0]
  · simp [thermalWeight]
  · intro n hn
    simp [thermalWeight, zero_pow hn]

/-- The exact requested thermal characteristic, proved on the full Schrödinger Hilbert space. -/
theorem schrodingerThermalDensity_characteristic
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (r : ℝ)
    (hr : r ∈ Set.Ico (0:ℝ) 1) (q p : ℝ) :
    (schrodingerThermalDensity Q r hr).characteristic q p =
      Complex.exp (-(((1+r)/(1-r))*(q^2/Q.ξ^2+Q.ξ^2*p^2)/4 : ℝ)) := by
  by_cases hz : r = 0
  · subst r
    rw [schrodingerThermalDensity_zero, oscillator_vacuum_characteristic]
    norm_num
  have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
  let a : ℝ := (1-r)/(2*r)
  have ha : 0 < a := div_pos (sub_pos.mpr hr.2) (mul_pos (by norm_num) hr0)
  have hc : circularRatio a = r := by
    unfold circularRatio a
    field_simp
    ring
  have hν : 1+1/a = (1+r)/(1-r) := by
    unfold a
    have hden : 1-r ≠ 0 := sub_ne_zero.mpr hr.2.ne'
    field_simp [hden]
    ring
  have hs : circularMixtureDensity Q a ha = schrodingerThermalDensity Q r hr := by
    simpa only [hc] using circularMixtureDensity_eq_schrodingerThermalDensity Q a ha
  rw [← hs, circularMixtureDensity_characteristic, hν]

/-- Gaussianity of the actual diagonal thermal density, without a thermal-orbit definition. -/
theorem schrodingerThermalDensity_isGaussian
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (r : ℝ)
    (hr : r ∈ Set.Ico (0:ℝ) 1) :
    IsGaussianWith (schrodingerThermalDensity Q r hr) 0
      (diagonalCovariance (((1+r)/(1-r))/Q.ξ^2) (((1+r)/(1-r))*Q.ξ^2)) := by
  refine ⟨diagonalCovariance_symm _ _, ?_⟩
  intro q p
  rw [schrodingerThermalDensity_characteristic]
  congr 1
  simp only [LinearMap.zero_apply, diagonalCovariance_apply, Complex.ofReal_zero,
    zero_mul, zero_sub]
  push_cast
  ring

/-- The same actual state now has both the proved Gaussian Weyl property and canonical CFC entropy. -/
theorem schrodingerThermalDensity_gaussian_entropy
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν) :
    IsGaussianWith (schrodingerThermalDensity Q (thermalRatio ν) (thermalRatio_mem hν)) 0
      (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2)) ∧
    (schrodingerThermalDensity Q (thermalRatio ν) (thermalRatio_mem hν)).entropy =
      ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  have he : (1+thermalRatio ν)/(1-thermalRatio ν) = ν := by
    unfold thermalRatio
    have hp : ν+1 ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, schrodingerThermalDensity_entropy_eq_boson Q hν⟩
  simpa only [he] using schrodingerThermalDensity_isGaussian Q (thermalRatio ν) (thermalRatio_mem hν)

end Gaussian.Physical.Boson
