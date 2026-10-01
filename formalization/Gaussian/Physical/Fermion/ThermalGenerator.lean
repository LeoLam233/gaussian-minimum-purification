import Gaussian.Physical.Fermion.CovarianceContraction
import Gaussian.Physical.Fermion.Thermal

noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem thermalGenerator_false (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n) :
    covarianceGenerator (thermal n t ht) (coefficientBasis n (i,false)) =
      t i • coefficientBasis n (i,true) := by
  ext a
  rcases a with ⟨j,b⟩
  change (∑ x : MajoranaIndex n, -covariance (thermal n t ht) (j,b) x *
    (coefficientBasis n (i,false)) x) = _
  simp only [coefficientBasis,PiLp.single_apply]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [thermal_covariance]
  cases b <;> by_cases h : i=j <;> simp_all [PiLp.smul_apply,PiLp.single_apply,eq_comm]

theorem thermalGenerator_true (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n) :
    covarianceGenerator (thermal n t ht) (coefficientBasis n (i,true)) =
      -t i • coefficientBasis n (i,false) := by
  ext a
  rcases a with ⟨j,b⟩
  change (∑ x : MajoranaIndex n, -covariance (thermal n t ht) (j,b) x *
    (coefficientBasis n (i,true)) x) = _
  simp only [coefficientBasis,PiLp.single_apply]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [thermal_covariance]
  cases b <;> by_cases h : i=j <;> simp_all [PiLp.smul_apply,PiLp.single_apply,eq_comm]

end Gaussian.Physical.Fermion
