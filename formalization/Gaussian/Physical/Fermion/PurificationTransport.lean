import Gaussian.Physical.Fermion.PurificationBlocks
import Gaussian.Physical.Fermion.CoefficientOrthogonality

noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

/-- Act on the physical real coordinates and leave the auxiliary coordinates fixed. -/
def physicalMatrixLift {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) : Matrix (d ⊕ d) (d ⊕ d) ℝ := Matrix.fromBlocks M 0 0 1

@[simp] theorem physicalMatrixLift_one {d : Type*} [Fintype d] [DecidableEq d] :
    physicalMatrixLift (1 : Matrix d d ℝ) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [physicalMatrixLift,Matrix.fromBlocks,Matrix.one_apply]

@[simp] theorem physicalMatrixLift_mul {d : Type*} [Fintype d] [DecidableEq d]
    (M N : Matrix d d ℝ) : physicalMatrixLift (M*N) = physicalMatrixLift M*physicalMatrixLift N := by
  simp [physicalMatrixLift,Matrix.fromBlocks_multiply]

@[simp] theorem physicalMatrixLift_transpose {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) : (physicalMatrixLift M)ᵀ = physicalMatrixLift Mᵀ := by
  simp [physicalMatrixLift,Matrix.fromBlocks_transpose]

theorem physicalMatrixLift_conjugate {d : Type*} [Fintype d] [DecidableEq d]
    (M N A B C D : Matrix d d ℝ) :
    physicalMatrixLift M * Matrix.fromBlocks A B C D * physicalMatrixLift N =
      Matrix.fromBlocks (M*A*N) (M*B) (C*N) D := by
  simp [physicalMatrixLift,Matrix.fromBlocks_multiply]

def rotatedPurificationBlock (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    Matrix (MajoranaIndex n ⊕ MajoranaIndex n) (MajoranaIndex n ⊕ MajoranaIndex n) ℝ :=
  physicalMatrixLift (coefficientMatrix R) * purificationBlock n t ht *
    physicalMatrixLift (coefficientMatrix R⁻¹)

theorem rotatedPurificationBlock_square (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    rotatedPurificationBlock n t ht R * rotatedPurificationBlock n t ht R = -1 := by
  unfold rotatedPurificationBlock
  calc
    _ = physicalMatrixLift (coefficientMatrix R) *
      (purificationBlock n t ht *
        (physicalMatrixLift (coefficientMatrix R⁻¹) * physicalMatrixLift (coefficientMatrix R)) *
          purificationBlock n t ht) * physicalMatrixLift (coefficientMatrix R⁻¹) := by
      noncomm_ring
    _ = -1 := by
      rw [← physicalMatrixLift_mul,coefficientMatrix_inverse_mul,physicalMatrixLift_one,
        Matrix.mul_one,purificationBlock_square,Matrix.mul_neg,Matrix.mul_one,Matrix.neg_mul,
        ← physicalMatrixLift_mul,coefficientMatrix_mul_inverse,physicalMatrixLift_one]

theorem rotatedPurificationBlock_transpose (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    (rotatedPurificationBlock n t ht R)ᵀ = -rotatedPurificationBlock n t ht R := by
  simp [rotatedPurificationBlock,Matrix.transpose_mul,purificationBlock_transpose,Matrix.mul_assoc]

theorem rotatedPurificationBlock_physical (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U)
    (a b : MajoranaIndex n) :
    rotatedPurificationBlock n t ht R (Sum.inl a) (Sum.inl b) =
      generatorMatrix ((thermal n t ht).uConj U) a b := by
  unfold rotatedPurificationBlock purificationBlock
  rw [physicalMatrixLift_conjugate,implemented_generatorMatrix_conjugate _ R U hU]
  rfl

end Gaussian.Physical.Fermion
