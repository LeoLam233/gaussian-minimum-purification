import Gaussian.Physical.Boson.VectorFamilyDensity

/-! Actual bounded-observable expectation sums for positive nuclear vector families. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normalVectorFamily_expect_hasSum {ι : Type*} (v : ι → H)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (A : H →L[ℂ] H) :
    HasSum (fun i => ⟪v i,A (v i)⟫_ℂ) ((normalVectorFamily v hv).expect A) := by
  have h := (summable_vectorOperator v hv.summable).hasSum.mapL (TraceClass.tracePairing A)
  simpa only [vectorOperator_pairing,NormalDensity.expect,normalVectorFamily] using h

theorem NormalDensity.sqrt_expect_hasSum (ρ : NormalDensity H)
    {w : Set H} (b : HilbertBasis w ℂ H) (A : H →L[ℂ] H) :
    HasSum (fun i : w => ⟪(CFC.sqrt ρ.operator.1) (b i),
      A ((CFC.sqrt ρ.operator.1) (b i))⟫_ℂ) (ρ.expect A) := by
  have h := normalVectorFamily_expect_hasSum
    (fun i : w => (CFC.sqrt ρ.operator.1) (b i)) (ρ.sqrt_vectors_hasSum b) A
  rw [← ρ.eq_normalVectorFamily_sqrt b] at h
  exact h

end Gaussian.Physical.Boson
