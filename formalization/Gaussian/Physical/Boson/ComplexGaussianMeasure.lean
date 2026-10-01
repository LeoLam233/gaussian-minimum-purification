import Gaussian.Physical.Boson.ComplexGaussianMoments

/-! A normalized complex-plane Gaussian measure, with exact integral transport.
It is an ordinary positive probability density, not a quantum-state assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped ENNReal

def complexGaussianPDF (a : ℝ) (z : ℂ) : ℝ :=
  (a/Real.pi)*Real.exp (-a*‖z‖^2)

lemma complexGaussianPDF_nonneg (a : ℝ) (ha : 0 < a) (z : ℂ) :
    0 ≤ complexGaussianPDF a z := by unfold complexGaussianPDF; positivity

theorem lintegral_complexGaussianPDF (a : ℝ) (ha : 0 < a) :
    (∫⁻ z : ℂ, ENNReal.ofReal (complexGaussianPDF a z)) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (complexGaussianPDF_nonneg a ha)) (by unfold complexGaussianPDF; fun_prop)]
  unfold complexGaussianPDF
  rw [integral_const_mul]
  have h := integral_complex_gaussian_radial a ha 0
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
    zero_add, pow_one, mul_one] at h
  rw [h]
  field_simp [ha.ne', Real.pi_ne_zero]

def complexGaussianMeasure (a : ℝ) (_ha : 0 < a) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (complexGaussianPDF a z))

instance complexGaussianMeasure_isProbability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (complexGaussianMeasure a ha) where
  measure_univ := by
    rw [complexGaussianMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_complexGaussianPDF a ha]

theorem integral_complexGaussianMeasure (a : ℝ) (ha : 0 < a) (f : ℂ → ℂ) :
    (∫ z, f z ∂complexGaussianMeasure a ha) =
      ∫ z, (complexGaussianPDF a z : ℂ)*f z := by
  rw [complexGaussianMeasure, integral_withDensity_eq_integral_toReal_smul
    (by unfold complexGaussianPDF; fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (complexGaussianPDF_nonneg a ha _), Complex.real_smul]

/-- The characteristic integral is obtained from the actual two-dimensional Gaussian integral. -/
theorem complexGaussianMeasure_characteristic (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∫ z : ℂ, Complex.exp ((inner ℝ w z : ℂ)*Complex.I) ∂complexGaussianMeasure a ha) =
      Complex.exp (-((‖w‖^2/(4*a) : ℝ):ℂ)) := by
  rw [integral_complexGaussianMeasure]
  have he (z : ℂ) : (complexGaussianPDF a z : ℂ) *
      Complex.exp ((inner ℝ w z : ℂ)*Complex.I) =
      ((a/Real.pi : ℝ):ℂ)*Complex.exp (-(a:ℂ)*(‖z‖:ℂ)^2+Complex.I*(inner ℝ w z : ℂ)) := by
    unfold complexGaussianPDF
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (b := (a:ℂ))
    (by simpa only [Complex.ofReal_re] using ha) Complex.I w]
  norm_num [Complex.finrank_real_complex, Complex.I_sq]
  have hac : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpc : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end Gaussian.Physical.Boson
