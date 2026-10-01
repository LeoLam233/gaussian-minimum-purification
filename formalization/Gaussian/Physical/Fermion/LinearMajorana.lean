import Gaussian.Physical.Fermion.TwoPoint
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def majoranaSum (n : ℕ) (v : MajoranaIndex n → ℂ) : Operator n :=
  ∑ a, v a • majorana n a

@[simp] theorem majoranaSum_add (n : ℕ) (v w : MajoranaIndex n → ℂ) :
    majoranaSum n (v+w) = majoranaSum n v + majoranaSum n w := by
  simp [majoranaSum, add_smul, Finset.sum_add_distrib]

@[simp] theorem majoranaSum_smul (n : ℕ) (r : ℂ) (v : MajoranaIndex n → ℂ) :
    majoranaSum n (r • v) = r • majoranaSum n v := by
  simp [majoranaSum, mul_smul, Finset.smul_sum]

theorem majoranaSum_car_generator (n : ℕ) (v : MajoranaIndex n → ℂ) (b : MajoranaIndex n) :
    majoranaSum n v * majorana n b + majorana n b * majoranaSum n v =
      (2 * v b) • (1 : Operator n) := by
  unfold majoranaSum
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, majorana_car]
  simp [smul_smul, mul_comm]

theorem majoranaSum_car (n : ℕ) (v w : MajoranaIndex n → ℂ) :
    majoranaSum n v * majoranaSum n w + majoranaSum n w * majoranaSum n v =
      (2 * ∑ a, v a * w a) • (1 : Operator n) := by
  conv_lhs => arg 1; arg 2; unfold majoranaSum
  conv_lhs => arg 2; arg 1; unfold majoranaSum
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, majoranaSum_car_generator]
  simp only [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem majoranaSum_square (n : ℕ) (v : MajoranaIndex n → ℂ) :
    majoranaSum n v * majoranaSum n v = (∑ a, v a * v a) • (1 : Operator n) := by
  have h := majoranaSum_car n v v
  have hh := congrArg (fun A : Operator n => (1/2 : ℂ) • A) h
  norm_num [smul_add, smul_smul, ← add_smul, ← mul_assoc] at hh
  exact hh

abbrev CoefficientSpace (n : ℕ) := EuclideanSpace ℝ (MajoranaIndex n)

def linearMajorana (n : ℕ) (v : CoefficientSpace n) : Operator n :=
  majoranaSum n (fun a => (v a : ℂ))

@[simp] theorem linearMajorana_hermitian (n : ℕ) (v : CoefficientSpace n) :
    (linearMajorana n v)ᴴ = linearMajorana n v := by
  simp [linearMajorana, majoranaSum, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]

@[simp] theorem linearMajorana_add (n : ℕ) (v w : CoefficientSpace n) :
    linearMajorana n (v+w) = linearMajorana n v + linearMajorana n w := by
  unfold linearMajorana
  convert majoranaSum_add n (fun a => (v a : ℂ)) (fun a => (w a : ℂ)) using 1
  congr 1; ext a; simp

@[simp] theorem linearMajorana_smul (n : ℕ) (r : ℝ) (v : CoefficientSpace n) :
    linearMajorana n (r • v) = (r : ℂ) • linearMajorana n v := by
  unfold linearMajorana
  convert majoranaSum_smul n (r : ℂ) (fun a => (v a : ℂ)) using 1
  congr 1; ext a; simp

@[simp] theorem linearMajorana_neg (n : ℕ) (v : CoefficientSpace n) :
    linearMajorana n (-v) = -linearMajorana n v := by
  simpa using linearMajorana_smul n (-1) v

theorem linearMajorana_car (n : ℕ) (v w : CoefficientSpace n) :
    linearMajorana n v * linearMajorana n w + linearMajorana n w * linearMajorana n v =
      (2 * (⟪v,w⟫ : ℝ) : ℂ) • (1 : Operator n) := by
  rw [linearMajorana, linearMajorana, majoranaSum_car]
  congr 1
  simp [PiLp.inner_apply, Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]

theorem linearMajorana_square (n : ℕ) (v : CoefficientSpace n) :
    linearMajorana n v * linearMajorana n v = (‖v‖^2 : ℝ) • (1 : Operator n) := by
  rw [linearMajorana, majoranaSum_square]
  have h : (∑ a, (v a : ℂ) * (v a : ℂ)) = ((‖v‖^2 : ℝ) : ℂ) := by
    have hr : (∑ a, v a * v a) = ‖v‖^2 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using
        (real_inner_self_eq_norm_sq v)
    exact_mod_cast hr
  rw [h]
  rfl

theorem linearMajorana_parity (n : ℕ) (v : CoefficientSpace n) :
    linearMajorana n v * parity n = -(parity n * linearMajorana n v) := by
  simp only [linearMajorana, majoranaSum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, majorana_parity, smul_neg, Finset.sum_neg_distrib]

end Gaussian.Physical.Fermion
