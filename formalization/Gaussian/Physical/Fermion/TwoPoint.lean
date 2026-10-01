import Gaussian.Physical.Fermion.Generation

noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

@[simp] theorem moment_pair {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    moment ρ [a,b] = (ρ.m * (majorana n a * majorana n b)).trace := by
  simp [moment, wordOperator]

theorem twoPoint_star {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    star (moment ρ [a,b]) = moment ρ [b,a] := by
  rw [moment_pair, moment_pair, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, majorana_hermitian, majorana_hermitian]
  have hρ : ρ.mᴴ = ρ.m := ρ.Hermitian
  rw [hρ, Matrix.trace_mul_comm]

theorem twoPoint_add_swap {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    moment ρ [a,b] + moment ρ [b,a] = if a=b then (2 : ℂ) else 0 := by
  rw [moment_pair, moment_pair, ← Matrix.trace_add, ← Matrix.mul_add, majorana_car]
  split_ifs <;> simp [Matrix.mul_smul, Matrix.trace_smul, ρ.tr']

theorem covariance_eq_im_twoPoint {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    covariance ρ a b = (moment ρ [a,b]).im := by
  unfold covariance
  rw [Matrix.mul_sub, Matrix.trace_sub, ← moment_pair, ← moment_pair,
    ← twoPoint_star, Complex.sub_im]
  simp only [Complex.star_def, Complex.conj_im]
  ring

theorem twoPoint_eq_delta_add_covariance {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    moment ρ [a,b] = (if a=b then (1 : ℂ) else 0) +
      Complex.I * (covariance ρ a b : ℂ) := by
  have hs := congrArg Complex.re (twoPoint_add_swap ρ a b)
  rw [← twoPoint_star ρ a b] at hs
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hs
  apply Complex.ext
  · by_cases h : a=b <;> simp [h, Complex.mul_re] at hs ⊢ <;> linarith
  · rw [covariance_eq_im_twoPoint]
    by_cases h : a=b <;> simp [h]

theorem quasifree_eq_of_covariance {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (hΓ : ∀ a b, covariance ρ a b = covariance σ a b) : ρ = σ := by
  apply quasifree_eq_of_twoPoint ρ σ hρ hσ
  intro a b
  rw [twoPoint_eq_delta_add_covariance, twoPoint_eq_delta_add_covariance, hΓ]

end Gaussian.Physical.Fermion
