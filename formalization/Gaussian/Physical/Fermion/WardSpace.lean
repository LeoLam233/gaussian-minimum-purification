import Gaussian.Physical.Fermion.WardAlgebra

/-! Linear structure of first-slot Wick recurrence and actual parity of matrix words. -/
noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For a fixed tail, heads satisfying Wick's recurrence form a genuine linear subspace. -/
def wordWardSpace (D : Matrix d d ℂ) (B : List (Matrix d d ℂ)) :
    Submodule ℂ (Matrix d d ℂ) where
  carrier := { A | (D*(A*B.prod)).trace = ∑ i : Fin B.length,
    (-1:ℂ)^i.val * (D*(A*B.get i)).trace * (D*(B.eraseIdx i.val).prod).trace }
  zero_mem' := by simp
  add_mem' := by
    intro A C hA hC
    change (D*((A+C)*B.prod)).trace = _
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    rw [hA,hC]
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  smul_mem' := by
    intro r A hA
    change (D*((r • A)*B.prod)).trace = _
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [hA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem weighted_head_mem_wordWardSpace (D A : Matrix d d ℂ) (p q : ℂ)
    (hD : D.trace=1) (hpq : p+q=1) (hbal : q • (D*A) = p • (A*D))
    (B : List (Matrix d d ℂ)) (s : Matrix d d ℂ → ℂ)
    (hCAR : ∀ X ∈ B, A*X+X*A=s X • 1) (hodd : Odd B.length) :
    A ∈ wordWardSpace D B := weighted_word_Ward D A p q hD hpq hbal B s hCAR hodd

theorem involution_conjugate_mul (P A B : Matrix d d ℂ) (hP : P*P=1) :
    P*(A*B)*P = (P*A*P)*(P*B*P) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P,hP,Matrix.one_mul]

/-- A product of odd matrices has the expected total parity. -/
theorem odd_word_conjugate (P : Matrix d d ℂ) (hP : P*P=1)
    (B : List (Matrix d d ℂ)) (hB : ∀ X ∈ B, P*X*P = -X) :
    P*B.prod*P = (-1:ℂ)^B.length • B.prod := by
  induction B with
  | nil => simp [hP]
  | cons b B ih =>
    rw [List.prod_cons, involution_conjugate_mul _ _ _ hP, hB b (by simp),
      ih (fun X hX => hB X (by simp [hX]))]
    rw [Matrix.mul_smul, Matrix.neg_mul, List.length_cons, pow_succ]
    simp [mul_comm]

/-- Parity invariance of a density matrix annihilates all odd operator-word expectations. -/
theorem trace_odd_word_zero (D P : Matrix d d ℂ) (hP : P*P=1)
    (hD : P*D*P=D) (B : List (Matrix d d ℂ))
    (hB : ∀ X ∈ B, P*X*P = -X) (hodd : Odd B.length) :
    (D*B.prod).trace = 0 := by
  have htransport : ((P*D*P)*B.prod).trace = (D*(P*B.prod*P)).trace := by
    calc
      ((P*D*P)*B.prod).trace = (P*(D*P*B.prod)).trace := by simp [Matrix.mul_assoc]
      _ = ((D*P*B.prod)*P).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp [Matrix.mul_assoc]
  rw [hD,odd_word_conjugate P hP B hB,hodd.neg_one_pow,neg_one_smul,
    Matrix.mul_neg,Matrix.trace_neg] at htransport
  have hzero : (2:ℂ)*(D*B.prod).trace = 0 := by linear_combination htransport
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- Heads whose anticommutator with a fixed operator is scalar form a linear subspace. -/
def scalarAnticommutant (B : Matrix d d ℂ) : Submodule ℂ (Matrix d d ℂ) where
  carrier := { A | ∃ z : ℂ, A*B+B*A=z • 1 }
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro A C ⟨z,hz⟩ ⟨w,hw⟩
    refine ⟨z+w,?_⟩
    calc
      (A+C)*B+B*(A+C) = (A*B+B*A)+(C*B+B*C) := by
        simp only [Matrix.add_mul,Matrix.mul_add]; abel
      _ = (z+w) • 1 := by rw [hz,hw,add_smul]
  smul_mem' := by
    rintro r A ⟨z,hz⟩
    refine ⟨r*z,?_⟩
    rw [Matrix.smul_mul,Matrix.mul_smul,← smul_add,hz,smul_smul]

/-- Scalar existence suffices; the contraction is extracted by an actual normalized trace. -/
theorem weighted_head_mem_of_scalar_anticommutators (D A : Matrix d d ℂ) (p q : ℂ)
    (hD : D.trace=1) (hpq : p+q=1) (hbal : q • (D*A) = p • (A*D))
    (B : List (Matrix d d ℂ)) (hCAR : ∀ X ∈ B, A ∈ scalarAnticommutant X)
    (hodd : Odd B.length) : A ∈ wordWardSpace D B := by
  apply weighted_head_mem_wordWardSpace D A p q hD hpq hbal B
    (fun X => (D*(A*X+X*A)).trace) ?_ hodd
  intro X hX
  obtain ⟨z,hz⟩ := hCAR X hX
  rw [hz,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul,hD]
  simp

end Gaussian.Physical.Fermion
