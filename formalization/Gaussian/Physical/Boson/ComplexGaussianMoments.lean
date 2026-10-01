import Gaussian.Physical.Boson.CoherentCoefficients
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Integral.Gamma

/-! Exact complex Gaussian monomial integrals. Off-diagonal cancellation is proved by an
actual volume-preserving rotation; all required Gaussian-polynomial integrability is proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped ComplexConjugate

lemma exists_circle_monomial_neg_one (m n : ℕ) (hmn : m ≠ n) :
    ∃ c : Circle, (c:ℂ)^m * (star (c:ℂ))^n = -1 := by
  let θ : ℝ := Real.pi / ((m:ℝ)-(n:ℝ))
  let c : Circle := ⟨Complex.exp ((θ:ℂ)*Complex.I), by
    simpa [Submonoid.unitSphere] using Complex.norm_exp_ofReal_mul_I θ⟩
  refine ⟨c, ?_⟩
  change Complex.exp ((θ:ℂ)*Complex.I)^m *
    (star (Complex.exp ((θ:ℂ)*Complex.I)))^n = -1
  rw [← Complex.exp_nat_mul, RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  have hd : (m:ℂ)-(n:ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have he : (m:ℂ)*((θ:ℂ)*Complex.I)+(n:ℂ)*
      (starRingEnd ℂ) ((θ:ℂ)*Complex.I) = (Real.pi:ℂ)*Complex.I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    dsimp [θ]
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_pi_mul_I]

/-- A radial weight kills distinct holomorphic/antiholomorphic monomial degrees. -/
theorem integral_radial_monomial_offDiagonal (g : ℝ → ℂ) (m n : ℕ) (hmn : m ≠ n) :
    (∫ z : ℂ, z^m * (star z)^n * g ‖z‖) = 0 := by
  obtain ⟨c,hc⟩ := exists_circle_monomial_neg_one m n hmn
  let f : ℂ → ℂ := fun z => z^m * (star z)^n * g ‖z‖
  have hr := (rotation c).measurePreserving.integral_comp
    (rotation c).toHomeomorph.measurableEmbedding f
  have he (z : ℂ) : f (rotation c z) = -f z := by
    simp only [f, rotation_apply, mul_pow, star_mul, norm_mul, Circle.norm_coe, one_mul]
    calc
      _ = ((c:ℂ)^m * (star (c:ℂ))^n) * (z^m * (star z)^n * g ‖z‖) := by ring
      _ = _ := by rw [hc]; ring
  simp_rw [he] at hr
  rw [integral_neg] at hr
  have hzero : (∫ z : ℂ, f z) = 0 := neg_eq_self.mp hr
  exact hzero

lemma integral_complex_gaussian_radial (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ z : ℂ, ‖z‖^(2*n) * Real.exp (-a*‖z‖^2)) =
      Real.pi * (n.factorial:ℝ) / a^(n+1) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (2*n:ℕ)) (b := a) (by norm_num) (lt_of_lt_of_le (by norm_num : (-2:ℝ) < 0) (Nat.cast_nonneg _)) ha
  have he : (((2*n:ℕ):ℝ)+2)/2 = (n:ℝ)+1 := by push_cast; ring
  rw [he, Real.Gamma_nat_eq_factorial] at h
  have he' : -(((2*n:ℕ):ℝ)+2)/2 = -((n+1:ℕ):ℝ) := by push_cast; ring
  rw [he'] at h
  convert h using 1
  · simp only [Real.rpow_natCast, Real.rpow_two]
  · rw [Real.rpow_neg, Real.rpow_natCast]
    ring
    exact ha.le

end Gaussian.Physical.Boson

namespace Gaussian.Physical.Boson
open MeasureTheory

/-- Absolute integrability of all complex Gaussian polynomial moments. -/
theorem integrable_complex_gaussian_monomial (a : ℝ) (ha : 0 < a) (m n : ℕ) :
    Integrable (fun z : ℂ => z^m * (star z)^n * (Real.exp (-a*‖z‖^2) : ℂ)) := by
  have hrad : Integrable (fun z : ℂ => ‖z‖^(m+n) * Real.exp (-a*‖z‖^2)) := by
    have hv := Complex.integral_rpow_mul_exp_neg_mul_rpow
      (p := 2) (q := ((m+n:ℕ):ℝ)) (b := a) (by norm_num) (lt_of_lt_of_le (by norm_num : (-2:ℝ) < 0) (Nat.cast_nonneg _)) ha
    have hp : 0 < (2*Real.pi/2) * a^(-(((m+n:ℕ):ℝ)+2)/2) *
        Real.Gamma ((((m+n:ℕ):ℝ)+2)/2) := by
      apply mul_pos
      · positivity
      · apply Real.Gamma_pos_of_pos
        positivity
    have hint : Integrable (fun z : ℂ => ‖z‖^((m+n:ℕ):ℝ) * Real.exp (-a*‖z‖^(2:ℝ))) := by
      by_contra h
      rw [integral_undef h] at hv
      rw [← hv] at hp
      exact lt_irrefl _ hp
    simpa only [Real.rpow_natCast, Real.rpow_two] using hint
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [norm_mul, norm_pow, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), pow_add] using hrad

/-- Exact diagonal and off-diagonal complex Gaussian moments. -/
theorem integral_complex_gaussian_monomial (a : ℝ) (ha : 0 < a) (m n : ℕ) :
    (∫ z : ℂ, z^m * (star z)^n * (Real.exp (-a*‖z‖^2) : ℂ)) =
      if m = n then ((Real.pi * (n.factorial:ℝ) / a^(n+1) : ℝ):ℂ) else 0 := by
  split_ifs with h
  · subst m
    have he (z : ℂ) : z^n * (star z)^n * (Real.exp (-a*‖z‖^2) : ℂ) =
        ((‖z‖^(2*n) * Real.exp (-a*‖z‖^2) : ℝ):ℂ) := by
      have hz : z * star z = ((‖z‖^2 : ℝ):ℂ) := by
        rw [RCLike.star_def, RCLike.mul_conj]
        norm_cast
      rw [← mul_pow, hz, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← pow_mul]
    simp_rw [he]
    rw [integral_complex_ofReal, integral_complex_gaussian_radial a ha n]
  · exact integral_radial_monomial_offDiagonal
      (fun r : ℝ => (Real.exp (-a*r^2) : ℂ)) m n h

end Gaussian.Physical.Boson
