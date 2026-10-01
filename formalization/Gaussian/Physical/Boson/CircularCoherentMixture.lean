import Gaussian.Physical.Boson.ComplexGaussianMeasure

/-! Actual coherent probability mixtures indexed by the complex oscillator amplitude.
Their characteristic and matrix coefficients are computed independently. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped InnerProductSpace

def coherentLabel (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (z : ℂ) : ℝ × ℝ :=
  (-Q.ξ*z.re, z.im/Q.ξ)

theorem coherentLabel_coefficient (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (n : ℕ) (z : ℂ) :
    ⟪oscillatorBasis Q n, coherentVector Q (coherentLabel Q z)⟫_ℂ =
      hermiteNormalization n * z^n * (Real.exp (-‖z‖^2/4) : ℂ) := by
  rw [coherentVector_coefficient]
  have hs : (Q.ξ:ℂ) ≠ 0 := by exact_mod_cast Q.ξ_pos.ne'
  have ht : -(((coherentLabel Q z).1 : ℝ):ℂ)/Q.ξ +
      (((coherentLabel Q z).2 : ℝ):ℂ)*Q.ξ*Complex.I = z := by
    calc
      _ = (z.re:ℂ)+(z.im:ℂ)*Complex.I := by
        unfold coherentLabel
        push_cast
        field_simp
      _ = z := Complex.re_add_im z
  have hn : (coherentLabel Q z).1^2/Q.ξ^2+Q.ξ^2*(coherentLabel Q z).2^2 = ‖z‖^2 := by
    unfold coherentLabel
    rw [Complex.sq_norm, Complex.normSq_apply]
    field_simp [Q.ξ_pos.ne']
  rw [ht, hn]
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat, neg_div]

theorem integrable_coherentLabel_density
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (fun z => (coherentDensity Q (coherentLabel Q z)).operator) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
  · exact ((continuous_coherentDensity_operator Q).comp (by unfold coherentLabel; fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    rw [NormalDensity.operator_traceNorm]

def circularMixtureDensity (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (a : ℝ) (ha : 0 < a) : NormalDensity (Schrodinger ℝ) :=
  probabilityMixture (complexGaussianMeasure a ha) (fun z => coherentDensity Q (coherentLabel Q z))
    (integrable_coherentLabel_density Q _)

lemma coherentLabel_characteristic (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (z : ℂ) (q p : ℝ) :
    (coherentDensity Q (coherentLabel Q z)).characteristic q p =
      Complex.exp (((inner ℝ ((p*Q.ξ : ℝ)+(q/Q.ξ : ℝ)*Complex.I) z):ℂ)*Complex.I) *
        Complex.exp (-((q^2/Q.ξ^2+Q.ξ^2*p^2)/4 : ℝ)) := by
  rw [coherentDensity_characteristic]
  congr 2
  congr 1
  simp [coherentLabel, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

lemma coherentDual_norm_sq (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (q p : ℝ) :
    ‖((p*Q.ξ : ℝ):ℂ)+((q/Q.ξ : ℝ):ℂ)*Complex.I‖^2 = q^2/Q.ξ^2+Q.ξ^2*p^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero]
  field_simp
  ring

/-- Gaussianity follows from the actual coherent probability integral, independently of its spectrum. -/
theorem circularMixtureDensity_characteristic
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (a : ℝ) (ha : 0 < a) (q p : ℝ) :
    (circularMixtureDensity Q a ha).characteristic q p =
      Complex.exp (-(((1+1/a)*(q^2/Q.ξ^2+Q.ξ^2*p^2))/4 : ℝ)) := by
  unfold circularMixtureDensity NormalDensity.characteristic
  rw [probabilityMixture_expect]
  change (∫ z, (coherentDensity Q (coherentLabel Q z)).characteristic q p
    ∂complexGaussianMeasure a ha) = _
  simp_rw [coherentLabel_characteristic]
  rw [integral_mul_const, complexGaussianMeasure_characteristic, coherentDual_norm_sq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Gaussian.Physical.Boson
