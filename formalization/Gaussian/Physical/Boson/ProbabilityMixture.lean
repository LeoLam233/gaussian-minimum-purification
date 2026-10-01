import Gaussian.Physical.Boson.Characteristic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual probability mixtures in the complete trace-class Banach space.
No Gaussian characteristic or spectral conclusion is assumed. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped ComplexOrder
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace X]

theorem NormalDensity.operator_traceNorm (ρ : NormalDensity H) :
    ‖ρ.operator‖ = 1 := by
  rw [TraceClass.norm_eq_traceNorm, traceNorm_eq_re_trace_of_nonneg ρ.operator ρ.nonneg,
    ρ.trace_one]
  rfl

def probabilityMixture (μ : Measure X) [IsProbabilityMeasure μ]
    (ρ : X → NormalDensity H) (hρ : Integrable (fun x => (ρ x).operator) μ) : NormalDensity H where
  operator := ∫ x, (ρ x).operator ∂μ
  nonneg := by
    have he := traceClassInclusion.integral_comp_comm hρ
    rw [traceClassInclusion_apply] at he
    rw [← he]
    exact integral_nonneg (fun x => (ρ x).nonneg)
  trace_one := by
    rw [← normalTrace.integral_comp_comm hρ]
    simp only [NormalDensity.trace_one]
    simp

theorem probabilityMixture_expect (μ : Measure X) [IsProbabilityMeasure μ]
    (ρ : X → NormalDensity H) (hρ : Integrable (fun x => (ρ x).operator) μ)
    (A : H →L[ℂ] H) :
    (probabilityMixture μ ρ hρ).expect A = ∫ x, (ρ x).expect A ∂μ :=
  (TraceClass.tracePairing A).integral_comp_comm hρ |>.symm

end Gaussian.Physical.Boson
