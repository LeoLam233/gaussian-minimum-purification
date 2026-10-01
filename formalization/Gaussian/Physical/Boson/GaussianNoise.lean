import Gaussian.Physical.Boson.WeylContinuity
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Concrete normal Gaussian states obtained by actual trace-class Gaussian coherent mixtures.
These are not defined to be equal to the diagonal thermal state. That spectral identification
remains a separate theorem, not an assumption in this construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory ProbabilityTheory
open scoped ComplexOrder InnerProductSpace ENNReal NNReal

/-- The concrete coherent vector density is precisely an actual Weyl conjugate of the vacuum. -/
theorem coherentDensity_eq_displace (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (z : ℝ × ℝ) :
    coherentDensity Q z =
      (vectorDensity (oscillatorBasis Q 0) ((oscillatorBasis Q).orthonormal.norm_eq_one 0)).displace z.1 z.2 := by
  exact (conjugate_vectorDensity (oscillatorBasis Q 0)
    ((oscillatorBasis Q).orthonormal.norm_eq_one 0) (weylOperator z.1 z.2)).symm

theorem coherentDensity_characteristic (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (z : ℝ × ℝ) (q p : ℝ) :
    (coherentDensity Q z).characteristic q p =
      Complex.exp (((q*z.2-p*z.1 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((q^2/Q.ξ^2+Q.ξ^2*p^2)/4 : ℝ)) := by
  rw [coherentDensity_eq_displace, NormalDensity.characteristic_displace,
    oscillator_vacuum_characteristic]
  congr 2
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  congr 1
  push_cast
  ring

/-- Independent real Gaussian displacement noise, with exact zero-variance endpoints allowed. -/
def gaussianNoiseMeasure (u v : ℝ≥0) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 u).prod (gaussianReal 0 v)

instance gaussianNoiseMeasure_isProbabilityMeasure (u v : ℝ≥0) :
    IsProbabilityMeasure (gaussianNoiseMeasure u v) := by
  unfold gaussianNoiseMeasure
  infer_instance

/-- Actual positive trace-class trace-one density; its integrability has been proved. -/
def gaussianNoiseDensity (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (u v : ℝ≥0) :
    NormalDensity (Schrodinger ℝ) :=
  probabilityMixture (gaussianNoiseMeasure u v) (coherentDensity Q)
    (integrable_coherentDensity Q (gaussianNoiseMeasure u v))

lemma gaussianNoiseMeasure_phase_integral (u v : ℝ≥0) (q p : ℝ) :
    (∫ z : ℝ × ℝ, Complex.exp (((q*z.2-p*z.1 : ℝ) : ℂ)*Complex.I)
      ∂gaussianNoiseMeasure u v) =
      Complex.exp (-(((u:ℝ)*p^2+(v:ℝ)*q^2)/2 : ℝ)) := by
  have he : (fun z : ℝ × ℝ => Complex.exp (((q*z.2-p*z.1 : ℝ) : ℂ)*Complex.I)) =
      fun z => Complex.exp ((((-p)*z.1 : ℝ) : ℂ)*Complex.I) *
        Complex.exp (((q*z.2 : ℝ) : ℂ)*Complex.I) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, gaussianNoiseMeasure]
  rw [integral_prod_mul (fun a : ℝ => Complex.exp ((((-p)*a : ℝ) : ℂ)*Complex.I))
    (fun b : ℝ => Complex.exp (((q*b : ℝ) : ℂ)*Complex.I))]
  simp only [Complex.ofReal_mul]
  rw [← charFun_apply_real (μ := gaussianReal 0 u) (-p),
    ← charFun_apply_real (μ := gaussianReal 0 v) q, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A genuinely normal Gaussian state's Weyl characteristic, including all finite noise strengths. -/
theorem gaussianNoiseDensity_characteristic (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (u v : ℝ≥0) (q p : ℝ) :
    (gaussianNoiseDensity Q u v).characteristic q p =
      Complex.exp (-(((1/Q.ξ^2+2*(v:ℝ))*q^2 + (Q.ξ^2+2*(u:ℝ))*p^2)/4 : ℝ)) := by
  unfold gaussianNoiseDensity NormalDensity.characteristic
  rw [probabilityMixture_expect]
  change (∫ z, (coherentDensity Q z).characteristic q p ∂gaussianNoiseMeasure u v) = _
  simp_rw [coherentDensity_characteristic]
  rw [integral_mul_const, gaussianNoiseMeasure_phase_integral, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped NNReal

/-- A genuine symmetric covariance bilinear form in one-mode Weyl coefficient coordinates. -/
def diagonalCovariance (a b : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) where
  toFun z :=
    { toFun := fun w => a*z.1*w.1+b*z.2*w.2
      map_add' w t := by change a*z.1*(w.1+t.1)+b*z.2*(w.2+t.2) = _; ring
      map_smul' c w := by
        change a*z.1*(c*w.1)+b*z.2*(c*w.2) = c*(a*z.1*w.1+b*z.2*w.2)
        ring }
  map_add' z t := by
    apply LinearMap.ext
    intro w
    change a*(z.1+t.1)*w.1+b*(z.2+t.2)*w.2 = (a*z.1*w.1+b*z.2*w.2)+(a*t.1*w.1+b*t.2*w.2)
    ring
  map_smul' c z := by
    apply LinearMap.ext
    intro w
    change a*(c*z.1)*w.1+b*(c*z.2)*w.2 = c*(a*z.1*w.1+b*z.2*w.2)
    ring

@[simp] theorem diagonalCovariance_apply (a b : ℝ) (z w : ℝ × ℝ) :
    diagonalCovariance a b z w = a*z.1*w.1+b*z.2*w.2 := rfl

theorem diagonalCovariance_symm (a b : ℝ) : (diagonalCovariance a b).IsSymm := by
  constructor
  intro z w
  simp only [diagonalCovariance_apply]
  ring

/-- Gaussianity here is proved using the actual Weyl characteristic of a normal density. -/
theorem gaussianNoiseDensity_isGaussian (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (u v : ℝ≥0) : IsGaussianWith (gaussianNoiseDensity Q u v) 0
      (diagonalCovariance (1/Q.ξ^2+2*(v:ℝ)) (Q.ξ^2+2*(u:ℝ))) := by
  refine ⟨diagonalCovariance_symm _ _, ?_⟩
  intro q p
  rw [gaussianNoiseDensity_characteristic]
  congr 1
  simp only [LinearMap.zero_apply, diagonalCovariance_apply, Complex.ofReal_zero,
    zero_mul, zero_sub]
  push_cast
  ring

/-- A normal Gaussian state for every finite one-mode Williamson parameter ν≥1. -/
def isotropicGaussianDensity (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (ν : ℝ) (hν : 1 ≤ ν) : NormalDensity (Schrodinger ℝ) :=
  gaussianNoiseDensity Q
    ⟨(ν-1)*Q.ξ^2/2, div_nonneg (mul_nonneg (sub_nonneg.mpr hν) (sq_nonneg _)) (by norm_num)⟩
    ⟨(ν-1)/(2*Q.ξ^2), div_nonneg (sub_nonneg.mpr hν) (by positivity)⟩

theorem isotropicGaussianDensity_characteristic
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν) (q p : ℝ) :
    (isotropicGaussianDensity Q ν hν).characteristic q p =
      Complex.exp (-((ν*(q^2/Q.ξ^2+Q.ξ^2*p^2))/4 : ℝ)) := by
  unfold isotropicGaussianDensity
  rw [gaussianNoiseDensity_characteristic]
  congr 1
  change -((((1/Q.ξ^2+2*((ν-1)/(2*Q.ξ^2)))*q^2 +
      (Q.ξ^2+2*((ν-1)*Q.ξ^2/2))*p^2)/4 : ℝ):ℂ) =
    -(((ν*(q^2/Q.ξ^2+Q.ξ^2*p^2))/4 : ℝ):ℂ)
  congr 2
  have hs : Q.ξ ≠ 0 := Q.ξ_pos.ne'
  field_simp
  ring

theorem isotropicGaussianDensity_isGaussian
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (ν : ℝ) (hν : 1 ≤ ν) :
    IsGaussianWith (isotropicGaussianDensity Q ν hν) 0
      (diagonalCovariance (ν/Q.ξ^2) (ν*Q.ξ^2)) := by
  refine ⟨diagonalCovariance_symm _ _, ?_⟩
  intro q p
  rw [isotropicGaussianDensity_characteristic]
  change Complex.exp (-((ν*(q^2/Q.ξ^2+Q.ξ^2*p^2))/4 : ℝ)) =
    Complex.exp ((0:ℂ)*Complex.I - (((ν/Q.ξ^2)*q*q+(ν*Q.ξ^2)*p*p : ℝ):ℂ)/4)
  congr 1
  push_cast
  ring

end Gaussian.Physical.Boson
