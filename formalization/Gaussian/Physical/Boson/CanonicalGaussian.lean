import Gaussian.Physical.Boson.CanonicalThermal

/-! Raw Gaussian Weyl property of the genuine finite-mode canonical thermal density,
with canonical entropy and actual purity proved for the same full operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp

theorem unitOscillator_thermal_characteristic (ν : ℝ) (hν : 1 ≤ ν) (q p : ℝ) :
    (schrodingerThermalDensity unitOscillator (thermalRatio ν) (thermalRatio_mem hν)).characteristic q p =
      Complex.exp (-((ν*(q^2+p^2)/4 : ℝ) : ℂ)) := by
  rw [(unitOscillator_thermal_gaussian ν hν).2]
  congr 1
  simp only [LinearMap.zero_apply,diagonalCovariance_apply,Complex.ofReal_zero,zero_mul,zero_sub]
  push_cast
  ring

/-- Exact characteristic on the full untruncated Hilbert space, for every finite number of modes. -/
theorem canonicalThermalDensity_characteristic {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (q p : CanonicalConfiguration n) :
    (canonicalThermalDensity ν hν).characteristic q p =
      Complex.exp (-(((∑ i : Fin n, ν i*((q i)^2+(p i)^2))/4 : ℝ) : ℂ)) := by
  induction n with
  | zero =>
      have hq : q=0 := Subsingleton.elim _ _
      have hp : p=0 := Subsingleton.elim _ _
      subst q
      subst p
      simp
  | succ n ih =>
      rw [canonicalThermalDensity_characteristic_succ,
        unitOscillator_thermal_characteristic (ν 0) (hν 0),ih,
        ← Complex.exp_add,Fin.sum_univ_succ]
      congr 1
      push_cast
      ring

/-- The state predicate is its actual Weyl characteristic; Gaussianity is a theorem of the constructed density. -/
theorem canonicalThermalDensity_isGaussian {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    IsGaussianWith (canonicalThermalDensity ν hν) 0 (canonicalCovariance ν) := by
  refine ⟨canonicalCovariance_symm ν,?_⟩
  intro q p
  rw [canonicalThermalDensity_characteristic,canonicalCovariance_quadratic]
  congr 1
  simp only [LinearMap.zero_apply,Complex.ofReal_zero,zero_mul,zero_sub,
    Complex.ofReal_div,Complex.ofReal_ofNat]

theorem canonicalThermalDensity_gaussian_entropy_purity {n : ℕ}
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    IsGaussianWith (canonicalThermalDensity ν hν) 0 (canonicalCovariance ν) ∧
      (canonicalThermalDensity ν hν).entropy=ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) ∧
      ((canonicalThermalDensity ν hν).IsPure ↔ ∀ i, ν i=1) :=
  ⟨canonicalThermalDensity_isGaussian ν hν,canonicalThermalDensity_entropy ν hν,
    canonicalThermalDensity_isPure_iff ν hν⟩

end Gaussian.Physical.Boson
