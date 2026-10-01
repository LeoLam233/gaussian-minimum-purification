import Gaussian.Physical.Fermion.CovarianceOperator

/-! The physical covariance contraction is derived from density positivity by
applying it to the complex CAR field c(v)+i c(w). -/
noncomputable section
open scoped Matrix RealInnerProductSpace ComplexOrder
namespace Gaussian.Physical.Fermion

theorem density_quadratic_expectation_nonneg {n : ℕ} (ρ : Density n) (A : Operator n) :
    0 ≤ (ρ.m*(Aᴴ*A)).trace.re := by
  have h := (ρ.psd.mul_mul_conjTranspose_same A).trace_nonneg
  rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm] at h
  exact (RCLike.nonneg_iff.mp h).1

/-- Complex-field positivity bounds the actual antisymmetric covariance form. -/
theorem covarianceForm_quadratic_bound {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    2*covarianceForm ρ v w ≤ ‖v‖^2+‖w‖^2 := by
  let A := linearMajorana n v + Complex.I • linearMajorana n w
  have hp := density_quadratic_expectation_nonneg ρ A
  have he : (ρ.m*(Aᴴ*A)).trace.re = ‖v‖^2+‖w‖^2-2*covarianceForm ρ v w := by
    dsimp [A]
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
      linearMajorana_hermitian,Complex.star_def,Complex.conj_I,
      Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul,linearMajorana_square,
      Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_add,Matrix.trace_smul,
      MState.tr',smul_eq_mul,Complex.add_re]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
      zero_mul,one_mul,neg_mul,zero_sub]
    simp only [Complex.add_im,Complex.neg_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_add,neg_neg,Complex.smul_re,Complex.smul_im,
      Complex.one_re,Complex.one_im,mul_zero,add_zero,smul_eq_mul,mul_one]
    change ‖v‖^2 + covarianceForm ρ w v + -(covarianceForm ρ v w + -(‖w‖^2)) = _
    rw [covarianceForm_skew ρ w v]
    ring
  rw [he] at hp
  linarith

/-- The actual left-slot CAR covariance generator is a contraction for every
finite density matrix, including all zero/pure modes. -/
theorem covarianceGenerator_contraction {n : ℕ} (ρ : Density n) (v : CoefficientSpace n) :
    ‖covarianceGenerator ρ v‖ ≤ ‖v‖ := by
  have h := covarianceForm_quadratic_bound ρ v (covarianceGenerator ρ v)
  rw [← covarianceGenerator_inner,real_inner_self_eq_norm_sq] at h
  have hs : ‖covarianceGenerator ρ v‖^2 ≤ ‖v‖^2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end Gaussian.Physical.Fermion
