import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NoncommRing

/-! Exact CAR word recursion in a complex algebra, with no state hypotheses. -/
noncomputable section
open scoped BigOperators
namespace Gaussian.Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Move A through a finite word when every anticommutator is scalar.
The tail terms retain their original order; no commutativity of operators is used. -/
theorem move_through_word (A : R) (s : R → ℂ) (B : List R)
    (hCAR : ∀ X ∈ B, A*X+X*A = s X • (1:R)) :
    A * B.prod = (-1:ℂ)^B.length • (B.prod*A) +
      ∑ i : Fin B.length, ((-1:ℂ)^i.val * s (B.get i)) • (B.eraseIdx i.val).prod := by
  induction B with
  | nil => simp
  | cons b B ih =>
    have hb : A*b = s b • (1:R) - b*A := by
      apply eq_sub_iff_add_eq.mpr
      exact hCAR b (by simp)
    have ht := ih (fun X hX => hCAR X (by simp [hX]))
    have he : A * (b * B.prod) = s b • B.prod - b * (A * B.prod) := by
      rw [← mul_assoc,hb,sub_mul,smul_mul_assoc,one_mul,mul_assoc]
    rw [List.prod_cons,he,ht]
    simp only [List.length_cons, Fin.sum_univ_succ]
    simp [pow_succ, mul_add, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc,
      List.eraseIdx_cons_succ, Finset.sum_neg_distrib] <;> abel
end Gaussian.Algebra
