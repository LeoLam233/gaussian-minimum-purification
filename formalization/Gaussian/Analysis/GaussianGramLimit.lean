import Gaussian.Entropy.Scalar
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! An exact one-sided derivative test for the Gaussian Weyl Gram expression.
No approximate-equality-to-purity inference is involved. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace Gaussian.Analysis

theorem right_deriv_nonneg_of_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hz : f 0=0) (hpos : ∀ t,0≤t → 0≤f t) : 0≤d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add,hz,sub_zero,smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t (le_of_lt ht))

def gramProfile (a b c d : ℝ) (u : ℝ) : ℝ :=
  4-2*Real.exp (-a*u/4)-2*Real.exp (-b*u/4)+
    2*Real.sin (c*u/2)*Real.exp (-d*u/4)

private theorem exp_linear_deriv (a : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-a*u/4)) (-a/4) 0 := by
  convert (((hasDerivAt_id (0:ℝ)).const_mul (-a/4)).exp) using 1
  · funext u
    congr 1
    simp only [id_eq]
    ring
  · simp

private theorem sin_linear_deriv (c : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (c*u/2)) (c/2) 0 := by
  convert (((hasDerivAt_id (0:ℝ)).const_mul (c/2)).sin) using 1
  · funext u
    congr 1
    simp only [id_eq]
    ring
  · simp

theorem gramProfile_deriv (a b c d : ℝ) :
    HasDerivAt (gramProfile a b c d) ((a+b)/2+c) 0 := by
  have h := (((hasDerivAt_const (0:ℝ) (4:ℝ)).sub ((exp_linear_deriv a).const_mul 2)).sub
    ((exp_linear_deriv b).const_mul 2)).add
      (((sin_linear_deriv c).mul (exp_linear_deriv d)).const_mul 2)
  convert h using 1
  · funext u
    dsimp [gramProfile]
    ring
  · simp
    ring

/-- Positivity of every actual small Weyl Gram square forces the exact
Robertson coefficient inequality; no uniform squeezing or strictness is assumed. -/
theorem gaussian_gram_coefficient_nonneg (a b c d : ℝ)
    (h : ∀ t : ℝ,0≤gramProfile a b c d (t^2)) : 0≤a+b+2*c := by
  have hp : ∀ u : ℝ,0≤u → 0≤gramProfile a b c d u := by
    intro u hu
    simpa only [Real.sq_sqrt hu] using h (Real.sqrt u)
  have hd := right_deriv_nonneg_of_nonneg (gramProfile_deriv a b c d)
    (by norm_num [gramProfile]) hp
  linarith

end Gaussian.Analysis
