import Gaussian.Physical.Boson.Observation

/-! Positivity of actual normal-density expectations of bounded Gram squares. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem NormalDensity.expect_star_mul_self_nonneg (ρ : NormalDensity H)
    (A : H →L[ℂ] H) : 0≤(ρ.expect (star A*A)).re := by
  let T : TraceClass H := TraceClass.ofOperator (A*ρ.operator.1*star A)
    (isTraceClass_mul_mul ρ.operator.2)
  have hT : 0≤T.1 := star_right_conjugate_nonneg ρ.nonneg A
  have hAR : IsTraceClass (A*ρ.operator.1) := TraceClass.isTraceClass_mul_coe A ρ.operator
  have hc := trace_mul_cycle (A := star A) hAR
  have he : ρ.expect (star A*A)=normalTrace T := by
    change trace ((star A*A)*ρ.operator.1) _=trace (A*ρ.operator.1*star A) _
    calc
      _=trace (star A*(A*ρ.operator.1)) _ := TraceClass.trace_transport (mul_assoc _ _ _) _
      _=_ := hc
  rw [he,← traceNorm_eq_re_trace_of_nonneg T hT]
  exact traceNorm_nonneg T.1 T.2

@[simp] theorem NormalDensity.expect_add (ρ : NormalDensity H) (A B : H →L[ℂ] H) :
    ρ.expect (A+B)=ρ.expect A+ρ.expect B := ρ.expectLinear.map_add A B

@[simp] theorem NormalDensity.expect_sub (ρ : NormalDensity H) (A B : H →L[ℂ] H) :
    ρ.expect (A-B)=ρ.expect A-ρ.expect B := ρ.expectLinear.map_sub A B

@[simp] theorem NormalDensity.expect_zero (ρ : NormalDensity H) :
    ρ.expect (0 : H →L[ℂ] H)=0 := ρ.expectLinear.map_zero

end Gaussian.Physical.Boson
