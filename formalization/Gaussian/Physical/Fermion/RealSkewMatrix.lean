import Gaussian.Physical.Fermion.PurityBridge

noncomputable section
open Gaussian.Phase
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem realMatrix_operator_skew {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) (hM : Mᵀ = -M) : IsSkew (Matrix.toEuclideanLin M) := by
  intro v w
  change (∑ a,w a*(∑ b,M a b*v b)) = -(∑ a,(∑ b,M a b*w b)*v a)
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hab : M b a = -M a b := congrFun₂ hM a b
  rw [hab]
  ring

theorem realMatrix_operator_square_neg {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) (hM : M*M = -1) (v : EuclideanSpace ℝ d) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin M v) = -v := by
  have hL : (Matrix.toEuclideanLin M).comp (Matrix.toEuclideanLin M) = -LinearMap.id := by
    rw [← Matrix.toLpLin_mul_same,hM]
    simp
  exact congrArg (fun L : EuclideanSpace ℝ d →ₗ[ℝ] EuclideanSpace ℝ d => L v) hL

theorem reindex_transpose_neg {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (M : Matrix d d ℝ) (hM : Mᵀ = -M) (q : d ≃ e) :
    (Matrix.reindexAlgEquiv ℝ ℝ q M)ᵀ = -(Matrix.reindexAlgEquiv ℝ ℝ q M) := by
  ext a b
  exact congrFun₂ hM (q.symm a) (q.symm b)

end Gaussian.Physical.Fermion
