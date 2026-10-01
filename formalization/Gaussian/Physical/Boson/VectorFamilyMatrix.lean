import Gaussian.Physical.Boson.VectorFamilyDensity

/-! Actual operator matrix coefficients of positive nuclear vector families. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def traceMatrixCoefficient (x y : H) : TraceClass H →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H y).comp traceClassInclusion)

@[simp] theorem traceMatrixCoefficient_apply (x y : H) (T : TraceClass H) :
    traceMatrixCoefficient x y T=⟪x,T.1 y⟫_ℂ := rfl

theorem traceMatrixCoefficient_vectorOperator (x y v : H) :
    traceMatrixCoefficient x y (vectorOperator v)=⟪x,v⟫_ℂ*⟪v,y⟫_ℂ := by
  change ⟪x,InnerProductSpace.rankOne ℂ v v y⟫_ℂ=_
  rw [InnerProductSpace.rankOne_apply,inner_smul_right,mul_comm]

theorem normalVectorFamily_matrix_hasSum {ι : Type*} (v : ι → H)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (x y : H) :
    HasSum (fun i => ⟪x,v i⟫_ℂ*⟪v i,y⟫_ℂ) ⟪x,(normalVectorFamily v hv).operator.1 y⟫_ℂ := by
  have h := (summable_vectorOperator v hv.summable).hasSum.mapL (traceMatrixCoefficient x y)
  change HasSum (fun i => traceMatrixCoefficient x y (vectorOperator (v i)))
    (traceMatrixCoefficient x y (∑' i,vectorOperator (v i))) at h
  simp only [traceMatrixCoefficient_vectorOperator] at h
  exact h

theorem NormalDensity.sqrt_matrix_hasSum (ρ : NormalDensity H)
    {w : Set H} (b : HilbertBasis w ℂ H) (x y : H) :
    HasSum (fun i : w => ⟪x,(CFC.sqrt ρ.operator.1) (b i)⟫_ℂ*
      ⟪(CFC.sqrt ρ.operator.1) (b i),y⟫_ℂ) ⟪x,ρ.operator.1 y⟫_ℂ := by
  have h := normalVectorFamily_matrix_hasSum
    (fun i : w => (CFC.sqrt ρ.operator.1) (b i)) (ρ.sqrt_vectors_hasSum b) x y
  change HasSum _ ⟪x,(∑' i : w,vectorOperator ((CFC.sqrt ρ.operator.1) (b i))).1 y⟫_ℂ at h
  rw [ρ.sqrt_vector_series b] at h
  exact h

end Gaussian.Physical.Boson
