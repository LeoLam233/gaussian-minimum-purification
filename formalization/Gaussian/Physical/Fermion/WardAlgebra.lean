import Gaussian.Algebra.CARWordRecursion
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Endpoint-safe Ward identities, derived from weighted matrix pull-through.
The weights only sum to one: either weight may vanish. -/
noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Weighted pull-through becomes weighted cyclicity of actual matrix expectations. -/
theorem weighted_trace_balance (D A P : Matrix d d ℂ) (p q : ℂ)
    (h : q • (D*A) = p • (A*D)) :
    q * (D*(A*P)).trace = p * (D*(P*A)).trace := by
  have he := congrArg (fun M : Matrix d d ℂ => (M*P).trace) h
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at he
  have hcyc : (A*D*P).trace = (D*(P*A)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rwa [Matrix.mul_assoc, hcyc] at he

/-- Scalar solving uses p+q=1 rather than an inverse thermal probability. -/
theorem weighted_trace_solve (T S C p q : ℂ) (hpq : p+q=1)
    (hbal : q*T=p*S) (hsum : T+S=C) : T=p*C := by
  calc
    T = (p+q)*T := by rw [hpq, one_mul]
    _ = p*T+p*S := by rw [add_mul, hbal]
    _ = p*(T+S) := by ring
    _ = p*C := by rw [hsum]

/-- The same balance fixes the two-point contraction. -/
theorem weighted_twoPoint (D A B : Matrix d d ℂ) (p q s : ℂ)
    (hD : D.trace=1) (hpq : p+q=1)
    (hbal : q • (D*A) = p • (A*D)) (hCAR : A*B+B*A=s • 1) :
    (D*(A*B)).trace = p*s := by
  apply weighted_trace_solve _ _ _ p q hpq (weighted_trace_balance D A B p q hbal)
  rw [← Matrix.trace_add, ← Matrix.mul_add, hCAR, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, hD]
  simp

/-- The actual Wick first-slot recurrence for any weighted annihilation-like head
and an odd tail of operators with scalar anticommutators. -/
theorem weighted_word_Ward (D A : Matrix d d ℂ) (p q : ℂ)
    (hD : D.trace=1) (hpq : p+q=1) (hbal : q • (D*A) = p • (A*D))
    (B : List (Matrix d d ℂ)) (s : Matrix d d ℂ → ℂ)
    (hCAR : ∀ X ∈ B, A*X+X*A=s X • 1) (hodd : Odd B.length) :
    (D*(A*B.prod)).trace = ∑ i : Fin B.length,
      (-1:ℂ)^i.val * (D*(A*B.get i)).trace * (D*(B.eraseIdx i.val).prod).trace := by
  have hm := Gaussian.Algebra.move_through_word A s B hCAR
  rw [hodd.neg_one_pow, neg_one_smul] at hm
  have ht := congrArg (fun M : Matrix d d ℂ => (D*M).trace) hm
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg,
    Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at ht
  have hsum : (D*(A*B.prod)).trace + (D*(B.prod*A)).trace =
      ∑ i : Fin B.length, (-1:ℂ)^i.val * s (B.get i) *
        (D*(B.eraseIdx i.val).prod).trace := by
    rw [ht]
    ring
  have hw := weighted_trace_solve _ _ _ p q hpq
    (weighted_trace_balance D A B.prod p q hbal) hsum
  rw [hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weighted_twoPoint D A (B.get i) p q (s (B.get i)) hD hpq hbal
    (hCAR (B.get i) (List.get_mem _ _))]
  ring

end Gaussian.Physical.Fermion
