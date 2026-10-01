import Gaussian.Physical.Boson.NormalEntropy

/-! Actual bounded-observable expectation and unitary covariance. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Expectation is linear in the actual bounded observable. -/
def NormalDensity.expectLinear (ρ : NormalDensity H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ ρ.operator).toLinearMap.comp TraceClass.tracePairingLinear

@[simp] theorem NormalDensity.expectLinear_apply (ρ : NormalDensity H) (A : H →L[ℂ] H) :
    ρ.expectLinear A = ρ.expect A := rfl

@[simp] theorem NormalDensity.expect_smul (ρ : NormalDensity H) (c : ℂ) (A : H →L[ℂ] H) :
    ρ.expect (c • A) = c * ρ.expect A := by
  exact ρ.expectLinear.map_smul c A

theorem NormalDensity.expect_conjugate (ρ : NormalDensity H)
    (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    (ρ.conjugate U).expect A = ρ.expect (star (U : H →L[ℂ] H) * A * (U : H →L[ℂ] H)) := by
  let T := ρ.operator.1
  let u : H →L[ℂ] H := U
  have hT : IsTraceClass T := ρ.operator.2
  have hAT : IsTraceClass (A*u*T) := by
    simpa using (isTraceClass_mul_mul (A := A*u) (B := 1) hT)
  have hc := trace_mul_cycle (A := star u) hAT
  change trace (A*(u*T*star u)) _ = trace ((star u*A*u)*T) _
  calc
    trace (A*(u*T*star u)) _ = trace ((A*u*T)*star u) _ :=
      TraceClass.trace_transport (by simp only [mul_assoc]) _
    _ = trace (star u*(A*u*T)) _ := hc.symm
    _ = trace ((star u*A*u)*T) _ := TraceClass.trace_transport (by simp only [mul_assoc]) _
end Gaussian.Physical.Boson
