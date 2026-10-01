import Gaussian.Physical.Boson.GaussianNoise
import Gaussian.Physical.Boson.HermiteGaussianIntegral

/-! Actual Hermite coefficients of displaced Schrödinger vacuum vectors.
This is a finite integral route toward identification of the normal Gaussian mixture
with the diagonal thermal density; no Mehler sum is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory Polynomial
open scoped InnerProductSpace

/-- Explicit pointwise Gaussian product for the actual Weyl-displaced vector. -/
theorem gaussian_coherent_weight (s C : ℝ) (hs : 0 < s) (ψ : Schrodinger ℝ)
    (hfun : ψ =ᵐ[volume] fun x : ℝ => ((C*Real.exp (-x^2/(2*s^2)) : ℝ):ℂ))
    (a b : ℝ) :
    (fun x : ℝ => ⟪ψ x, weyl a b ψ x⟫_ℂ) =ᵐ[volume]
      fun x => ((C:ℂ)^2 * Complex.exp (((-a^2/(2*s^2):ℝ):ℂ)+((b*a/2:ℝ):ℂ)*Complex.I)) *
        Complex.exp (-((x/s:ℝ):ℂ)^2 +
          (-(a:ℂ)/s+(b:ℂ)*s*Complex.I)*((x/s:ℝ):ℂ)) := by
  have hshift := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp hfun
  filter_upwards [hfun, hshift, weyl_ae a b ψ] with x hx hax hw
  simp only [Function.comp_apply] at hax
  rw [hw, hx, hax]
  have hreal (r : ℝ) : (starRingEnd ℂ) (r:ℂ) = (r:ℂ) := Complex.conj_ofReal r
  simp only [RCLike.inner_apply, hreal]
  simp only [phase, weylPhase, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Complex.ofReal_mul, Complex.ofReal_exp]
  calc
    _ = (C:ℂ)^2 * (Complex.exp (((x*b+a*b/2:ℝ):ℂ)*Complex.I) *
        Complex.exp ((-(x+a)^2/(2*s^2):ℝ):ℂ) *
        Complex.exp ((-x^2/(2*s^2):ℝ):ℂ)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add, mul_assoc, ← Complex.exp_add]
      congr 1
      congr 1
      have hsc : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      push_cast
      field_simp
      ring

/-- The scalar normalization of the nth oscillator eigenfunction relative to the vacuum. -/
def hermiteNormalization (n : ℕ) : ℂ := ((1/Real.sqrt (2^n*(n.factorial:ℝ)) : ℝ):ℂ)

lemma oscillatorBasis_ae (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    oscillatorBasis Q n =ᵐ[volume] Q.eigenfunction n := by
  rw [oscillatorBasis_apply]
  exact QuantumMechanics.OneDimension.HilbertSpace.coe_mk_ae (Q.eigenfunction_memHS n)

lemma oscillator_vacuum_ae (Q : QuantumMechanics.OneDimension.HarmonicOscillator) :
    oscillatorBasis Q 0 =ᵐ[volume] fun x : ℝ =>
      (((1/Real.sqrt (Real.sqrt Real.pi*Q.ξ))*Real.exp (-x^2/(2*Q.ξ^2)) : ℝ):ℂ) := by
  filter_upwards [oscillatorBasis_ae Q 0] with x hx
  rw [hx, Q.eigenfunction_zero]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- Pointwise relative eigenfunction identity, so no series differentiation is needed. -/
lemma oscillatorBasis_relative_ae (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    oscillatorBasis Q n =ᵐ[volume] fun x : ℝ => hermiteNormalization n *
      (((physHermite n).aeval (x/Q.ξ) : ℝ):ℂ) * oscillatorBasis Q 0 x := by
  filter_upwards [oscillatorBasis_ae Q n, oscillatorBasis_ae Q 0] with x hn h0
  rw [hn, h0, Q.eigenfunction_eq_mul_eigenfunction_zero]
  rfl

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open MeasureTheory Polynomial
open scoped InnerProductSpace

lemma inner_oscillatorBasis_relative (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (n : ℕ) (f : Schrodinger ℝ) :
    ⟪oscillatorBasis Q n, f⟫_ℂ = hermiteNormalization n *
      ∫ x : ℝ, (((physHermite n).aeval (x/Q.ξ) : ℝ):ℂ) *
        ⟪oscillatorBasis Q 0 x, f x⟫_ℂ := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [oscillatorBasis_relative_ae Q n] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, hermiteNormalization, map_mul, Complex.conj_ofReal]
  ring

/-- Every occupation coefficient of an actual displaced Schrödinger vacuum.
The formula is derived by finite Hermite integration, with no assumed Fock ansatz. -/
theorem coherentVector_coefficient (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (n : ℕ) (a b : ℝ) :
    ⟪oscillatorBasis Q n, coherentVector Q (a,b)⟫_ℂ =
      hermiteNormalization n * (-(a:ℂ)/Q.ξ+(b:ℂ)*Q.ξ*Complex.I)^n *
        Complex.exp (-((a^2/Q.ξ^2+Q.ξ^2*b^2)/4 : ℝ)) := by
  let ψ := oscillatorBasis Q 0
  let w : ℝ → ℂ := fun x => ⟪ψ x, weyl a b ψ x⟫_ℂ
  let t : ℂ := -(a:ℂ)/Q.ξ+(b:ℂ)*Q.ξ*Complex.I
  let D : ℂ := (((1/Real.sqrt (Real.sqrt Real.pi*Q.ξ) : ℝ):ℂ)^2 *
    Complex.exp (((-a^2/(2*Q.ξ^2):ℝ):ℂ)+((b*a/2:ℝ):ℂ)*Complex.I))
  let e : ℝ → ℂ := fun x => Complex.exp (-((x/Q.ξ:ℝ):ℂ)^2+t*((x/Q.ξ:ℝ):ℂ))
  have hw : w =ᵐ[volume] fun x => D*e x :=
    gaussian_coherent_weight Q.ξ (1/Real.sqrt (Real.sqrt Real.pi*Q.ξ)) Q.ξ_pos ψ
      (oscillator_vacuum_ae Q) a b
  have hj : (∫ x : ℝ, (((physHermite n).aeval (x/Q.ξ) : ℝ):ℂ)*w x) =
      t^n * ∫ x : ℝ, w x := by
    calc
      _ = ∫ x : ℝ, D*((((physHermite n).aeval (x/Q.ξ) : ℝ):ℂ)*e x) := by
        apply integral_congr_ae
        filter_upwards [hw] with x hx
        rw [hx]
        ring
      _ = D*(t^n * ∫ x : ℝ, e x) := by
        rw [integral_const_mul, integral_scaled_physHermite_cexp_gaussian]
      _ = t^n * (D * ∫ x : ℝ, e x) := by ring
      _ = t^n * ∫ x : ℝ, w x := by rw [integral_congr_ae hw, integral_const_mul]
  have hw0 : (∫ x : ℝ, w x) =
      (vectorDensity ψ ((oscillatorBasis Q).orthonormal.norm_eq_one 0)).characteristic a b := by
    rw [NormalDensity.characteristic, vectorDensity_expect, L2.inner_def]
    rfl
  rw [inner_oscillatorBasis_relative]
  change hermiteNormalization n * (∫ x : ℝ, (((physHermite n).aeval (x/Q.ξ) : ℝ):ℂ)*w x) = _
  rw [hj, hw0, oscillator_vacuum_characteristic]
  simp only [t, mul_assoc]

end Gaussian.Physical.Boson
