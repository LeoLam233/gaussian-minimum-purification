import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Entrywise complexification of real matrices, preserving actual two-sided
inverse identities and transporting bases without orthogonality hypotheses. -/
noncomputable section
open Module
open scoped Matrix
namespace Gaussian.Spectral

def complexifyMatrix {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℂ := fun i j => (M i j : ℂ)

@[simp] theorem complexifyMatrix_mul {m n k : Type*} [Fintype n]
    (M : Matrix m n ℝ) (N : Matrix n k ℝ) :
    complexifyMatrix (M*N) = complexifyMatrix M * complexifyMatrix N := by
  ext i j
  simp [complexifyMatrix,Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]

@[simp] theorem complexifyMatrix_one {n : Type*} [DecidableEq n] :
    complexifyMatrix (1 : Matrix n n ℝ) = 1 := by
  ext i j
  by_cases h : i=j <;> simp [complexifyMatrix,Matrix.one_apply,h]

@[simp] theorem complexifyMatrix_mulVec_real {m n : Type*} [Fintype n]
    (M : Matrix m n ℝ) (x : n → ℝ) :
    complexifyMatrix M *ᵥ (fun j => (x j : ℂ)) = fun i => ((M*ᵥx) i : ℂ) := by
  ext i
  simp [complexifyMatrix,Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul]

/-- An actual real inverse pair gives an actual complex linear equivalence. -/
def complexifyLinearEquiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) (N : Matrix n m ℝ) (hMN : M*N=1) (hNM : N*M=1) :
    (n → ℂ) ≃ₗ[ℂ] (m → ℂ) :=
  Matrix.toLin'OfInv (M := complexifyMatrix N) (M' := complexifyMatrix M)
    (by rw [← complexifyMatrix_mul,hNM,complexifyMatrix_one])
    (by rw [← complexifyMatrix_mul,hMN,complexifyMatrix_one])

@[simp] theorem complexifyLinearEquiv_apply {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) (N : Matrix n m ℝ) (hMN : M*N=1) (hNM : N*M=1) (x : n → ℂ) :
    complexifyLinearEquiv M N hMN hNM x = complexifyMatrix M *ᵥ x := rfl

@[simp] theorem complexifyLinearEquiv_symm_apply {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) (N : Matrix n m ℝ) (hMN : M*N=1) (hNM : N*M=1) (x : m → ℂ) :
    (complexifyLinearEquiv M N hMN hNM).symm x = complexifyMatrix N *ᵥ x := rfl

/-- A complex basis may be transported through any real invertible matrix,
including nonorthogonal symplectic normal-form matrices. -/
def complexifyBasis {d ι : Type*} [Fintype d] [DecidableEq d]
    (M N : Matrix d d ℝ) (hMN : M*N=1) (hNM : N*M=1) (b : Basis ι ℂ (d → ℂ)) :
    Basis ι ℂ (d → ℂ) := b.map (complexifyLinearEquiv M N hMN hNM)

@[simp] theorem complexifyBasis_apply {d ι : Type*} [Fintype d] [DecidableEq d]
    (M N : Matrix d d ℝ) (hMN : M*N=1) (hNM : N*M=1) (b : Basis ι ℂ (d → ℂ)) (i : ι) :
    complexifyBasis M N hMN hNM b i = complexifyMatrix M *ᵥ b i := rfl

end Gaussian.Spectral
