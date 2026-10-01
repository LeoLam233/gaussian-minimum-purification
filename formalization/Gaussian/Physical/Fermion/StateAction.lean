import Gaussian.Physical.Fermion.OrthogonalAction

noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion

abbrev coefficientBasis (n : ℕ) (a : MajoranaIndex n) : CoefficientSpace n :=
  EuclideanSpace.single a 1

@[simp] theorem linearMajorana_basis (n : ℕ) (a : MajoranaIndex n) :
    linearMajorana n (coefficientBasis n a) = majorana n a := by
  simp [linearMajorana, majoranaSum, coefficientBasis, PiLp.single_apply]

/-- The actual covariance bilinear form, directly measured in linear CAR fields. -/
def covarianceForm {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) : ℝ :=
  (ρ.m * (linearMajorana n v * linearMajorana n w)).trace.im

@[simp] theorem covarianceForm_basis {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    covarianceForm ρ (coefficientBasis n a) (coefficientBasis n b) = covariance ρ a b := by
  rw [covariance_eq_im_twoPoint, moment_pair]
  simp [covarianceForm]

/-- The trace-defined covariance form is represented by the trace-defined covariance matrix. -/
theorem covarianceForm_matrix {n : ℕ} (ρ : Density n) (v w : CoefficientSpace n) :
    covarianceForm ρ v w = ∑ a, ∑ b, v a * w b * covariance ρ a b := by
  unfold covarianceForm linearMajorana majoranaSum
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.im_sum]
  simp only [smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.im_sum, ← moment_pair, ← covariance_eq_im_twoPoint]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Actual unitary conjugation transports all observable expectations. -/
theorem unitaryState_expectation {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    ((ρ.uConj U).m * A).trace = (ρ.m * ((U : Matrix d d ℂ)ᴴ * A * U)).trace := by
  change (((U : Matrix d d ℂ) * ρ.m * (U : Matrix d d ℂ)ᴴ) * A).trace = _
  calc
    (((U : Matrix d d ℂ) * ρ.m * (U : Matrix d d ℂ)ᴴ) * A).trace =
        ((U : Matrix d d ℂ) * (ρ.m * (U : Matrix d d ℂ)ᴴ * A)).trace := by
          simp [Matrix.mul_assoc]
    _ = ((ρ.m * (U : Matrix d d ℂ)ᴴ * A) * U).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp [Matrix.mul_assoc]

/-- Conjugation by an actual unitary respects operator products. -/
theorem unitary_conjugate_mul {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A B : Matrix d d ℂ) :
    (U : Matrix d d ℂ) * (A * B) * (U : Matrix d d ℂ)ᴴ =
      ((U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)ᴴ) *
      ((U : Matrix d d ℂ) * B * (U : Matrix d d ℂ)ᴴ) := by
  have hleft : (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 := U.property.1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix d d ℂ)ᴴ (U : Matrix d d ℂ), hleft, Matrix.one_mul]

/-- The physical orthogonal action transports the actual covariance bilinear form. -/
theorem implemented_covarianceForm {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U)
    (v w : CoefficientSpace n) :
    covarianceForm (ρ.uConj U) v w = covarianceForm ρ (R⁻¹ v) (R⁻¹ w) := by
  unfold covarianceForm
  rw [unitaryState_expectation]
  have hi := implements_inv n hU
  have hm := unitary_conjugate_mul U⁻¹ (linearMajorana n v) (linearMajorana n w)
  change (U : Operator n)ᴴ * (linearMajorana n v * linearMajorana n w) *
      ((U : Operator n)ᴴ)ᴴ = _ at hm
  rw [Matrix.conjTranspose_conjTranspose] at hm
  rw [hm, hi v, hi w]

/-- Covariance entries are a proved orthogonal compression of actual state covariance. -/
theorem implemented_covariance {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U)
    (a b : MajoranaIndex n) :
    covariance (ρ.uConj U) a b =
      ∑ i, ∑ j, (R⁻¹ (coefficientBasis n a)) i *
        (R⁻¹ (coefficientBasis n b)) j * covariance ρ i j := by
  rw [← covarianceForm_basis, implemented_covarianceForm ρ R U hU, covarianceForm_matrix]

/-- Actual entropy preservation, with no Gaussian or covariance-level premise. -/
theorem unitaryState_entropy {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) : Sᵥₙ (ρ.uConj U) = Sᵥₙ ρ := by
  simp [Sᵥₙ]

/-- Actual purity preservation for the same physical action. -/
theorem unitaryState_pure_iff {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    (∃ ψ, ρ.uConj U = MState.pure ψ) ↔ ∃ ψ, ρ = MState.pure ψ := by
  rw [MState.pure_iff_constant_spectrum, MState.pure_iff_constant_spectrum]
  simp

end Gaussian.Physical.Fermion
