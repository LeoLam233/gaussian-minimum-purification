import Gaussian.Physical.Fermion.ModeMoves

/-! Covariance and correlations are read from actual finite density matrices.
Wick/quasifree Gaussianity is a raw property of all observable moments; entropy,
realizability, and subsystem formulas are not definition fields. -/
noncomputable section
open scoped Matrix Kronecker BigOperators
namespace Gaussian.Physical.Fermion

abbrev MajoranaIndex (n : ℕ) := Fin n × Bool

/-- The ordered product of actual signed Majorana observables. -/
def wordOperator (n : ℕ) (l : List (MajoranaIndex n)) : Operator n :=
  (l.map (majorana n)).prod

/-- Actual density-matrix moments. -/
def moment {n : ℕ} (ρ : Density n) (l : List (MajoranaIndex n)) : ℂ :=
  (ρ.m * wordOperator n l).trace

/-- Real antisymmetric covariance, with Γ_ab = -i/2 ⟨[c_a,c_b]⟩. -/
def covariance {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) : ℝ :=
  ((ρ.m * (majorana n a * majorana n b - majorana n b * majorana n a)).trace).im / 2

@[simp] theorem covariance_self {n : ℕ} (ρ : Density n) (a : MajoranaIndex n) :
    covariance ρ a a = 0 := by simp [covariance]

theorem covariance_skew {n : ℕ} (ρ : Density n) (a b : MajoranaIndex n) :
    covariance ρ a b = -covariance ρ b a := by
  unfold covariance
  rw [← neg_sub (majorana n a * majorana n b), Matrix.mul_neg, Matrix.trace_neg,
    Complex.neg_im, neg_div, neg_neg]

@[simp] theorem moment_nil {n : ℕ} (ρ : Density n) : moment ρ [] = 1 := by
  simp [moment, wordOperator, ρ.tr']

@[simp] theorem wordOperator_cons {n : ℕ} (a : MajoranaIndex n) (l : List (MajoranaIndex n)) :
    wordOperator n (a :: l) = majorana n a * wordOperator n l := by
  simp [wordOperator]

/-- Conjugation by a self-inverse matrix is multiplicative. -/
theorem conjugate_mul {d : Type*} [Fintype d] [DecidableEq d]
    (U A B : Matrix d d ℂ) (hU : U * U = 1) :
    U * (A * B) * U = (U * A * U) * (U * B * U) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U U, hU, Matrix.one_mul]

/-- Word parity is proved from the matrix CAR representation. -/
theorem wordOperator_parity (n : ℕ) (l : List (MajoranaIndex n)) :
    parity n * wordOperator n l * parity n = (-1 : ℂ) ^ l.length • wordOperator n l := by
  induction l with
  | nil => simp [wordOperator]
  | cons a l ih =>
    rw [wordOperator_cons, conjugate_mul _ _ _ (parity_square n), ih]
    have ha : parity n * majorana n a * parity n = -majorana n a := by
      rw [(neg_eq_iff_eq_neg.mpr (majorana_parity n a)).symm, Matrix.neg_mul,
        Matrix.mul_assoc, parity_square, Matrix.mul_one]
    rw [ha, Matrix.mul_smul, Matrix.neg_mul, List.length_cons, pow_succ]
    simp [mul_comm]

/-- Trace transport through actual self-inverse conjugation. -/
theorem trace_conjugate_product {d : Type*} [Fintype d] [DecidableEq d]
    (U R A : Matrix d d ℂ) :
    ((U * R * U) * A).trace = (R * (U * A * U)).trace := by
  calc
    ((U * R * U) * A).trace = (U * (R * U * A)).trace := by simp [Matrix.mul_assoc]
    _ = ((R * U * A) * U).trace := Matrix.trace_mul_comm _ _
    _ = (R * (U * A * U)).trace := by simp [Matrix.mul_assoc]

/-- Parity-invariant actual states have the required even/odd correlation symmetry. -/
theorem moment_parity {n : ℕ} (ρ : Density n) (hρ : ParityInvariant ρ)
    (l : List (MajoranaIndex n)) :
    moment ρ l = (-1 : ℂ) ^ l.length * moment ρ l := by
  unfold moment
  nth_rw 1 [← hρ]
  rw [trace_conjugate_product, wordOperator_parity, Matrix.mul_smul, Matrix.trace_smul]
  rfl

/-- All odd Majorana moments vanish, for every parity-invariant density state. -/
theorem moment_odd_zero {n : ℕ} (ρ : Density n) (hρ : ParityInvariant ρ)
    (l : List (MajoranaIndex n)) (hl : Odd l.length) : moment ρ l = 0 := by
  have h := moment_parity ρ hρ l
  rw [hl.neg_one_pow, neg_one_mul] at h
  have hm : (2 : ℂ) * moment ρ l = 0 := by linear_combination h
  exact (mul_eq_zero.mp hm).resolve_left (by norm_num)

end Gaussian.Physical.Fermion
