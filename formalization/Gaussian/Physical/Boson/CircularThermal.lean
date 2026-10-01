import Gaussian.Physical.Boson.CircularCoherentMixture
import Gaussian.Physical.Boson.DiagonalEntropy

/-! Identification of the actual coherent Gaussian mixture with the full diagonal thermal density.
This bridge uses bounded Hilbert matrix coefficients, avoiding point evaluation of L² integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped InnerProductSpace

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace X]

lemma probabilityMixture_matrixCoefficient (μ : Measure X) [IsProbabilityMeasure μ]
    (ρ : X → NormalDensity H) (hρ : Integrable (fun x => (ρ x).operator) μ) (v w : H) :
    ⟪v, (probabilityMixture μ ρ hρ).operator.1 w⟫_ℂ =
      ∫ x, ⟪v, (ρ x).operator.1 w⟫_ℂ ∂μ := by
  let L : TraceClass H →L[ℂ] ℂ := (innerSL ℂ v).comp
    ((ContinuousLinearMap.apply ℂ H w).comp traceClassInclusion)
  exact (L.integral_comp_comm hρ).symm

lemma hermiteNormalization_conj (n : ℕ) :
    (starRingEnd ℂ) (hermiteNormalization n) = hermiteNormalization n := by
  unfold hermiteNormalization
  exact Complex.conj_ofReal _

lemma hermiteNormalization_sq_factorial (n : ℕ) :
    (hermiteNormalization n)^2 * (n.factorial:ℂ) = 1/(2:ℂ)^n := by
  unfold hermiteNormalization
  have hr : (1/Real.sqrt (2^n*(n.factorial:ℝ)))^2*(n.factorial:ℝ) = 1/(2:ℝ)^n := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hrc := congrArg Complex.ofReal hr
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hrc

lemma coherentLabel_matrixCoefficient (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (m n : ℕ) (z : ℂ) :
    ⟪oscillatorBasis Q m, (coherentDensity Q (coherentLabel Q z)).operator.1 (oscillatorBasis Q n)⟫_ℂ =
      (hermiteNormalization m * hermiteNormalization n) *
        (z^m * (star z)^n * (Real.exp (-‖z‖^2/2) : ℂ)) := by
  change ⟪oscillatorBasis Q m, InnerProductSpace.rankOne ℂ
    (coherentVector Q (coherentLabel Q z)) (coherentVector Q (coherentLabel Q z)) (oscillatorBasis Q n)⟫_ℂ = _
  rw [InnerProductSpace.rankOne_apply, inner_smul_right,
    ← inner_conj_symm (coherentVector Q (coherentLabel Q z)) (oscillatorBasis Q n),
    coherentLabel_coefficient, coherentLabel_coefficient]
  simp only [map_mul, map_pow, hermiteNormalization_conj, Complex.conj_ofReal]
  have he : ((Real.exp (-‖z‖^2/4) : ℂ))^2 = (Real.exp (-‖z‖^2/2) : ℂ) := by
    norm_cast
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (hermiteNormalization m * hermiteNormalization n) *
      (z^m * (star z)^n * ((Real.exp (-‖z‖^2/4) : ℂ))^2) := by
        simp only [RCLike.star_def]
        ring
    _ = _ := by rw [he]

/-- The extra vacuum factor changes the radial inverse variance by exactly 1/2. -/
lemma complexGaussianMeasure_weighted_monomial (a : ℝ) (ha : 0 < a) (m n : ℕ) :
    (∫ z : ℂ, z^m * (star z)^n * (Real.exp (-‖z‖^2/2) : ℂ) ∂complexGaussianMeasure a ha) =
      (a/Real.pi : ℂ) *
        (if m = n then ((Real.pi*(n.factorial:ℝ)/(a+1/2)^(n+1) : ℝ):ℂ) else 0) := by
  rw [integral_complexGaussianMeasure]
  have he (z : ℂ) : (complexGaussianPDF a z : ℂ) *
      (z^m * (star z)^n * (Real.exp (-‖z‖^2/2) : ℂ)) =
      (a/Real.pi : ℂ) * (z^m * (star z)^n * (Real.exp (-(a+1/2)*‖z‖^2) : ℂ)) := by
    unfold complexGaussianPDF
    push_cast
    calc
      _ = (a/Real.pi : ℂ) * (z^m * (star z)^n *
        (Complex.exp (-(a:ℂ)*(‖z‖:ℂ)^2) * Complex.exp (-((‖z‖:ℂ)^2)/2))) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 3
        ring
  simp_rw [he]
  rw [integral_const_mul, integral_complex_gaussian_monomial (a+1/2) (by linarith) m n]

/-- All Hilbert matrix coefficients of the actual normal mixture are diagonal. -/
theorem circularMixtureDensity_matrixCoefficient
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (a : ℝ) (ha : 0 < a) (m n : ℕ) :
    ⟪oscillatorBasis Q m, (circularMixtureDensity Q a ha).operator.1 (oscillatorBasis Q n)⟫_ℂ =
      if m = n then (a/(2^n*(a+1/2)^(n+1)) : ℂ) else 0 := by
  unfold circularMixtureDensity
  rw [probabilityMixture_matrixCoefficient]
  simp_rw [coherentLabel_matrixCoefficient]
  rw [integral_const_mul, complexGaussianMeasure_weighted_monomial]
  split_ifs with h
  · subst m
    have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a:ℂ)+1/2 ≠ 0 := by
      intro h
      have hre : a+(1:ℝ)/2 = 0 := by simpa using congrArg Complex.re h
      linarith
    push_cast
    calc
      _ = ((hermiteNormalization n)^2 * (n.factorial:ℂ)) *
          ((a:ℂ)/((a:ℂ)+1/2)^(n+1)) := by field_simp
      _ = _ := by
        rw [hermiteNormalization_sq_factorial]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  · simp

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped InnerProductSpace

def circularRatio (a : ℝ) : ℝ := (2*a+1)⁻¹

theorem circularRatio_mem (a : ℝ) (ha : 0 < a) : circularRatio a ∈ Set.Ico (0:ℝ) 1 := by
  unfold circularRatio
  constructor
  · positivity
  · apply (inv_lt_one₀ (by linarith : 0 < 2*a+1)).mpr
    linarith

lemma circular_weight_eq_thermalWeight (a : ℝ) (ha : 0 < a) (n : ℕ) :
    a/(2^n*(a+1/2)^(n+1)) = thermalWeight (circularRatio a) n := by
  unfold thermalWeight circularRatio
  have hden : 2*a+1 ≠ 0 := by linarith
  have hplus : a+(1:ℝ)/2 = (2*a+1)/2 := by ring
  rw [hplus, div_pow, pow_succ]
  simp only [inv_pow]
  field_simp
  ring

/-- All occupation vectors are proved eigenvectors of the actual probability mixture. -/
theorem circularMixtureDensity_eigenvector
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (circularMixtureDensity Q a ha).operator.1 (oscillatorBasis Q n) =
      (thermalWeight (circularRatio a) n : ℂ) • oscillatorBasis Q n := by
  apply (oscillatorBasis Q).repr.injective
  apply lp.ext
  funext m
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_smul_right,
    circularMixtureDensity_matrixCoefficient]
  have hw := circular_weight_eq_thermalWeight a ha n
  by_cases h : m = n
  · subst m
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, (oscillatorBasis Q).orthonormal.norm_eq_one]
    norm_num
    have hcw := congrArg Complex.ofReal hw
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one,
      Nat.cast_pow, Nat.cast_ofNat] using hcw
  · rw [ite_eq_right h, (oscillatorBasis Q).orthonormal.inner_eq_zero h, mul_zero]

/-- The independently constructed normal Gaussian mixture equals the full thermal density operator. -/
theorem circularMixtureDensity_eq_schrodingerThermalDensity
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (a : ℝ) (ha : 0 < a) :
    circularMixtureDensity Q a ha =
      schrodingerThermalDensity Q (circularRatio a) (circularRatio_mem a ha) := by
  apply NormalDensity.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (oscillatorBasis Q).dense_span)
  rintro _ ⟨n,rfl⟩
  rw [circularMixtureDensity_eigenvector]
  exact (normalMixture_eigenvector (thermalWeight (circularRatio a))
    (thermalWeight_nonneg (circularRatio_mem a ha)) (hasSum_thermalWeight (circularRatio_mem a ha))
    (oscillatorBasis Q) n).symm

end Gaussian.Physical.Boson
