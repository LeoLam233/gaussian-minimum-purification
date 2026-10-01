import Gaussian.Physical.Boson.ThermalCharacteristic

/-! A fixed genuine oscillator basis of unit characteristic length.
This is only a canonical reference; physical Gaussian states retain arbitrary covariance and squeezing. -/
noncomputable section
namespace Gaussian.Physical.Boson
open Constants

def unitOscillator : QuantumMechanics.OneDimension.HarmonicOscillator where
  m := ℏ
  ω := 1
  hω := by norm_num
  hm := ℏ_pos

@[simp] theorem unitOscillator_length : unitOscillator.ξ=1 := by
  change Real.sqrt (ℏ/(ℏ*1))=1
  rw [mul_one,div_self ℏ_pos.ne',Real.sqrt_one]

def unitOscillatorBasis : HilbertBasis ℕ ℂ (Schrodinger ℝ) := oscillatorBasis unitOscillator

theorem unitOscillator_thermal_gaussian (ν : ℝ) (hν : 1 ≤ ν) :
    IsGaussianWith (schrodingerThermalDensity unitOscillator (thermalRatio ν) (thermalRatio_mem hν)) 0
      (diagonalCovariance ν ν) := by
  simpa only [unitOscillator_length,one_pow,div_one,mul_one] using
    (schrodingerThermalDensity_gaussian_entropy unitOscillator ν hν).1

end Gaussian.Physical.Boson
