import Gaussian.Physical.Boson.OscillatorBasis
import Gaussian.Physical.Boson.GaussianPredicate
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Direct Schrödinger wavefunction calculation of a pure Gaussian characteristic. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace

theorem gaussian_vector_characteristic_raw (s C : ℝ) (hs : 0 < s)
    (ψ : Schrodinger ℝ) (hψ : ‖ψ‖ = 1)
    (hfun : ψ =ᵐ[volume] fun x : ℝ => ((C * Real.exp (-x^2/(2*s^2)) : ℝ) : ℂ))
    (q p : ℝ) :
    (vectorDensity ψ hψ).characteristic q p =
      (C:ℂ)^2 * ((Real.pi : ℂ) / (1/(s:ℂ)^2)) ^ (1/2:ℂ) *
        Complex.exp (-((q^2/s^2+s^2*p^2)/4 : ℝ)) := by
  rw [NormalDensity.characteristic, vectorDensity_expect]
  change ⟪ψ, weyl q p ψ⟫_ℂ = _
  rw [L2.inner_def]
  have hshift := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp hfun
  have hint : (fun x : ℝ => ⟪ψ x, weyl q p ψ x⟫_ℂ) =ᵐ[volume]
      fun x => (C:ℂ)^2 * Complex.exp
        (((-1/s^2:ℝ):ℂ)*(x:ℂ)^2 + (((-q/s^2:ℝ):ℂ)+(p:ℂ)*Complex.I)*(x:ℂ) +
          (((-q^2/(2*s^2):ℝ):ℂ)+((p*q/2:ℝ):ℂ)*Complex.I)) := by
    filter_upwards [hfun, hshift, weyl_ae q p ψ] with x hx hqx hw
    simp only [Function.comp_apply] at hqx
    rw [hw, hx, hqx]
    have hreal (r : ℝ) : (starRingEnd ℂ) (r:ℂ) = (r:ℂ) := Complex.conj_ofReal r
    simp only [RCLike.inner_apply, hreal]
    simp only [phase, weylPhase, RCLike.inner_apply, starRingEnd_apply, star_trivial,
      Complex.ofReal_mul, Complex.ofReal_exp]
    calc
      _ = (C:ℂ)^2 * (Complex.exp (((x*p+q*p/2:ℝ):ℂ)*Complex.I) *
        Complex.exp ((-(x+q)^2/(2*s^2):ℝ):ℂ) *
        Complex.exp ((-x^2/(2*s^2):ℝ):ℂ)) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
  rw [integral_congr_ae hint, integral_const_mul]
  have hb : (((-1/s^2:ℝ):ℂ)).re < 0 := by
    simp only [Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hs)
  rw [integral_cexp_quadratic hb]
  have hden : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hphase : (((-q^2/(2*s^2):ℝ):ℂ)+((p*q/2:ℝ):ℂ)*Complex.I) -
      (((-q/s^2:ℝ):ℂ)+(p:ℂ)*Complex.I)^2/(4*((-1/s^2:ℝ):ℂ)) =
      -(((q^2/s^2+s^2*p^2)/4:ℝ):ℂ) := by
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  rw [hphase]
  push_cast
  ring

theorem gaussian_vector_characteristic (s C : ℝ) (hs : 0 < s)
    (ψ : Schrodinger ℝ) (hψ : ‖ψ‖ = 1)
    (hfun : ψ =ᵐ[volume] fun x : ℝ => ((C * Real.exp (-x^2/(2*s^2)) : ℝ) : ℂ))
    (q p : ℝ) :
    (vectorDensity ψ hψ).characteristic q p =
      Complex.exp (-((q^2/s^2+s^2*p^2)/4 : ℝ)) := by
  have hzero := gaussian_vector_characteristic_raw s C hs ψ hψ hfun 0 0
  simp only [NormalDensity.characteristic_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, mul_zero, add_zero, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one] at hzero
  rw [gaussian_vector_characteristic_raw s C hs ψ hψ hfun q p, ← hzero, one_mul]

theorem oscillator_vacuum_characteristic (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (q p : ℝ) :
    (vectorDensity (oscillatorBasis Q 0) ((oscillatorBasis Q).orthonormal.norm_eq_one 0)).characteristic q p =
      Complex.exp (-((q^2/Q.ξ^2+Q.ξ^2*p^2)/4 : ℝ)) := by
  apply gaussian_vector_characteristic Q.ξ (1/Real.sqrt (Real.sqrt Real.pi * Q.ξ)) Q.ξ_pos
  rw [oscillatorBasis_apply]
  have h := QuantumMechanics.OneDimension.HilbertSpace.coe_mk_ae (Q.eigenfunction_memHS 0)
  filter_upwards [h] with x hx
  rw [hx, Q.eigenfunction_zero]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]

end Gaussian.Physical.Boson
