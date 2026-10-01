import Gaussian.Physical.Fermion.ThermalPurity
import Gaussian.Physical.Fermion.CovarianceOperator
import Gaussian.Spectral.HermitianEigenbasis
import Gaussian.Spectral.PairEigenbasis
import Gaussian.Attainment.FermionicCuts

/-! The actual canonical covariance's independent Hermitian spectrum and CFC
cost are identified by an explicit complex eigenbasis, not spectral stipulation. -/
noncomputable section
open Module
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion

abbrev pairEigenEquiv (n : ℕ) := Gaussian.Spectral.pairEigenEquiv n
abbrev thermalPairBasis (n : ℕ) := Gaussian.Spectral.pairEigenbasis n

theorem thermalPairBasis_apply (n : ℕ) (i j : Fin n) (a b : Bool) :
    thermalPairBasis n (i,a) (j,b) =
      if i=j then (if b then (if a then Complex.I else -Complex.I) else 1) else 0 :=
  Gaussian.Spectral.pairEigenbasis_apply n i j a b

theorem thermalHermitian_mulVec_false (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (v : MajoranaIndex n → ℂ) (i : Fin n) :
    (hermitianCovariance (thermal n t ht) *ᵥ v) (i,false) = Complex.I*t i*v (i,true) := by
  simp [hermitianCovariance,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    thermal_covariance,apply_ite,mul_ite,ite_mul,Finset.sum_ite_eq',eq_comm]

theorem thermalHermitian_mulVec_true (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (v : MajoranaIndex n → ℂ) (i : Fin n) :
    (hermitianCovariance (thermal n t ht) *ᵥ v) (i,true) = -Complex.I*t i*v (i,false) := by
  simp [hermitianCovariance,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    thermal_covariance,apply_ite,mul_ite,ite_mul,Finset.sum_ite_eq',eq_comm]

theorem thermalHermitian_eigenvector (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (a : MajoranaIndex n) :
    hermitianCovariance (thermal n t ht) *ᵥ thermalPairBasis n a =
      ((if a.2 then -t a.1 else t a.1 : ℝ) : ℂ) • thermalPairBasis n a := by
  rcases a with ⟨i,b⟩
  ext ⟨j,c⟩
  cases c
  · rw [thermalHermitian_mulVec_false]
    simp only [thermalPairBasis_apply,Pi.smul_apply,smul_eq_mul]
    cases b <;> by_cases h : i=j <;> simp_all [eq_comm] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · rw [thermalHermitian_mulVec_true]
    simp only [thermalPairBasis_apply,Pi.smul_apply,smul_eq_mul]
    cases b <;> by_cases h : i=j <;> simp_all [eq_comm] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The independent Hermitian covariance CFC cost equals the once-per-mode entropy sum. -/
theorem thermal_hermitianCost (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) :
    Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat (thermal n t ht)) =
      ∑ i, Gaussian.Entropy.fermion (t i) := by
  rw [Gaussian.Attainment.fermionHermitianCost,
    Gaussian.Spectral.hermitian_trace_cfc_eq_eigenbasis_sum
      (covarianceHermitianMat (thermal n t ht)) (thermalPairBasis n)
      (fun a => if a.2 then -t a.1 else t a.1)
      (thermalHermitian_eigenvector n t ht)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,ite_true,
    Bool.false_eq_true,ite_false,abs_neg,fermion_scalar_abs,fermion_scalar_neg,Finset.sum_add_distrib]
  ring

end Gaussian.Physical.Fermion
