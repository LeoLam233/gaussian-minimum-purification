import Gaussian.Physical.Boson.VacuumCharacteristic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Finite Hermite–Gaussian integral identities for the coherent-mixture/thermal spectral bridge.
These analytic identities are proved before any identification with the diagonal thermal density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory Polynomial
open scoped InnerProductSpace

/-- Polynomial times a Gaussian with any finite complex linear term is integrable. -/
theorem integrable_polynomial_cexp_gaussian (P : Polynomial ℤ) (t : ℂ) :
    Integrable (fun x : ℝ => ((P.aeval x : ℝ):ℂ) * Complex.exp (-(x:ℂ)^2+t*x)) := by
  have hbase := Polynomial.guassian_integrable_polynomial (by norm_num : (0:ℝ) < 1/2) P
  apply Integrable.mono' (hbase.norm.const_mul (Real.exp (t.re^2/2)))
  · have hp : Continuous (fun x : ℝ => ((P.aeval x : ℝ):ℂ) * Complex.exp (-(x:ℂ)^2+t*x)) := by fun_prop
    exact hp.aestronglyMeasurable
  filter_upwards with x
  have he : -x^2+t.re*x ≤ -x^2/2+t.re^2/2 := by nlinarith [sq_nonneg (x-t.re)]
  have hr : (-(x:ℂ)^2+t*x).re = -x^2+t.re*x := by
    simp [pow_two, Complex.mul_re]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hr]
  calc
    |P.aeval x| * Real.exp (-x^2+t.re*x) ≤
        |P.aeval x| * Real.exp (-x^2/2+t.re^2/2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (abs_nonneg _)
    _ = Real.exp (t.re^2/2) * (|P.aeval x| * |Real.exp (-(1/2)*x^2)|) := by
      rw [Real.exp_add, abs_of_pos (Real.exp_pos _), show -(1/2:ℝ)*x^2 = -x^2/2 by ring]
      ring

/-- Complex differentiation of a real-coefficient polynomial restricted to the real axis. -/
lemma hasDerivAt_complex_aeval (P : Polynomial ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((P.aeval y : ℝ):ℂ)) ((P.derivative.aeval x : ℝ):ℂ) x := by
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (P.hasDerivAt_aeval x)

lemma hasDerivAt_cexp_gaussian (t : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(y:ℂ)^2+t*y))
      ((-2*(x:ℂ)+t)*Complex.exp (-(x:ℂ)^2+t*x)) x := by
  convert (((Complex.ofReal_hasDerivAt (x := x)).pow 2).neg.add
    ((Complex.ofReal_hasDerivAt (x := x)).const_mul t)).cexp using 1
  simp only [Pi.add_apply, Pi.neg_apply, Pi.pow_apply]
  ring

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open MeasureTheory Polynomial

/-- Integration by parts against a complex-shifted Gaussian, with every integrability
and differentiation obligation discharged. -/
theorem integral_polynomial_gaussian_raising (P : Polynomial ℤ) (t : ℂ) :
    (∫ x : ℝ, ((2*x*(P.aeval x : ℝ)-(P.derivative.aeval x : ℝ) : ℝ):ℂ) *
      Complex.exp (-(x:ℂ)^2+t*x)) =
    t * ∫ x : ℝ, ((P.aeval x : ℝ):ℂ) * Complex.exp (-(x:ℂ)^2+t*x) := by
  let u : ℝ → ℂ := fun x => ((P.aeval x : ℝ):ℂ)
  let du : ℝ → ℂ := fun x => ((P.derivative.aeval x : ℝ):ℂ)
  let v : ℝ → ℂ := fun x => Complex.exp (-(x:ℂ)^2+t*x)
  let dv : ℝ → ℂ := fun x => (-2*(x:ℂ)+t)*v x
  have hc : Integrable (fun x => u x*v x) := integrable_polynomial_cexp_gaussian P t
  have hb : Integrable (fun x => du x*v x) := integrable_polynomial_cexp_gaussian P.derivative t
  have hx : Integrable (fun x : ℝ => (x:ℂ)*u x*v x) := by
    have heval (x : ℝ) : ((X*P).aeval x : ℝ) = x*(P.aeval x : ℝ) :=
      (map_mul (aeval x : Polynomial ℤ →ₐ[ℤ] ℝ) X P).trans (by rw [aeval_X])
    have h := integrable_polynomial_cexp_gaussian (X*P) t
    simp only [heval, Complex.ofReal_mul] at h
    exact h
  have ha : Integrable (fun x => u x*dv x) := by
    convert (hx.const_mul (-2)).add (hc.const_mul t) using 1
    funext x
    dsimp [u, dv, v]
    ring
  have hip : (∫ x : ℝ, u x*dv x) = -∫ x : ℝ, du x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hasDerivAt_complex_aeval P x)
      (fun x _ => hasDerivAt_cexp_gaussian t x) ha hb hc
  have he : (fun x : ℝ => ((2*x*(P.aeval x : ℝ)-(P.derivative.aeval x : ℝ) : ℝ):ℂ) *
      Complex.exp (-(x:ℂ)^2+t*x)) =
      fun x => t*(u x*v x) - ((u x*dv x)+(du x*v x)) := by
    funext x
    dsimp [u, du, v, dv]
    push_cast
    ring
  rw [he]
  calc
    _ = (∫ x : ℝ, t*(u x*v x)) - ∫ x : ℝ, u x*dv x+du x*v x :=
      integral_sub (hc.const_mul t) (ha.add hb)
    _ = t*(∫ x : ℝ, u x*v x) - ((∫ x : ℝ, u x*dv x)+(∫ x : ℝ, du x*v x)) :=
      congrArg₂ (fun (a b : ℂ) => a-b) (integral_const_mul t _) (integral_add ha hb)
    _ = _ := by rw [hip]; ring

/-- A finite Hermite–Gaussian integral identity. No interchange of an infinite Mehler series
with an integral is involved. -/
theorem integral_physHermite_cexp_gaussian (n : ℕ) (t : ℂ) :
    (∫ x : ℝ, (((physHermite n).aeval x : ℝ):ℂ) * Complex.exp (-(x:ℂ)^2+t*x)) =
      t^n * ∫ x : ℝ, Complex.exp (-(x:ℂ)^2+t*x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he (x : ℝ) : ((physHermite (n+1)).aeval x : ℝ) =
        2*x*((physHermite n).aeval x : ℝ)-((physHermite n).derivative.aeval x : ℝ) := by
      simpa only [Polynomial.deriv_aeval] using physHermite_succ_apply n x
    simp_rw [he]
    rw [integral_polynomial_gaussian_raising, ih, pow_succ]
    ring

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open MeasureTheory Polynomial

/-- The Hermite integral recurrence transported through any finite positive oscillator length. -/
theorem integral_scaled_physHermite_cexp_gaussian (n : ℕ) (t : ℂ) (s : ℝ) :
    (∫ x : ℝ, (((physHermite n).aeval (x/s) : ℝ):ℂ) *
      Complex.exp (-((x/s:ℝ):ℂ)^2+t*((x/s:ℝ):ℂ))) =
    t^n * ∫ x : ℝ, Complex.exp (-((x/s:ℝ):ℂ)^2+t*((x/s:ℝ):ℂ)) := by
  have hn := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => (((physHermite n).aeval y : ℝ):ℂ) * Complex.exp (-(y:ℂ)^2+t*y)) s⁻¹
  have h0 := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp (-(y:ℂ)^2+t*y)) s⁻¹
  simp only [inv_inv, ← div_eq_inv_mul] at hn h0
  rw [hn, integral_physHermite_cexp_gaussian, h0]
  simp only [Complex.real_smul]
  ring

end Gaussian.Physical.Boson
