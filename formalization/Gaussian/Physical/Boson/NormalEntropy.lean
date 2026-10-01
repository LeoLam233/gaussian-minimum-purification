import Gaussian.Physical.Boson.NormalDensity
import Gaussian.Entropy.Scalar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! Extended von Neumann entropy via the positive CFC operator -ρ log ρ.
The value is infinity when that positive operator is not trace class.
No Gaussian spectral entropy formula or finiteness is assumed. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace ENNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_eq_re_trace_of_nonneg (T : TraceClass H) (hT : 0 ≤ T.1) :
    traceNorm T.1 T.2 = (normalTrace T).re := by
  obtain ⟨ι,b,_⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis T.2 b, normalTrace_apply, trace_eq_of_hilbertBasis T.2 b]
  rw [Complex.re_tsum (summable_trace_diagonal_of_isTraceClass T.2 b)]
  apply tsum_congr
  intro i
  rw [CFC.abs_of_nonneg T.1 hT]

theorem NormalDensity.operator_norm_le_one (ρ : NormalDensity H) : ‖ρ.operator.1‖ ≤ 1 := by
  have h := opNorm_le_traceNorm ρ.operator.2
  rw [traceNorm_eq_re_trace_of_nonneg ρ.operator ρ.nonneg, ρ.trace_one] at h
  exact h

def NormalDensity.entropyOperator (ρ : NormalDensity H) : H →L[ℂ] H :=
  cfc Real.negMulLog ρ.operator.1

theorem NormalDensity.entropyOperator_nonneg (ρ : NormalDensity H) : 0 ≤ ρ.entropyOperator := by
  apply cfc_nonneg
  intro x hx
  apply Real.negMulLog_nonneg
  · exact spectrum_nonneg_of_nonneg ρ.nonneg hx
  · calc
      x ≤ ‖x‖ := le_abs_self x
      _ ≤ ‖ρ.operator.1‖ * ‖(1 : H →L[ℂ] H)‖ := spectrum.norm_le_norm_mul_of_mem hx
      _ ≤ 1 * 1 := mul_le_mul ρ.operator_norm_le_one ContinuousLinearMap.norm_id_le
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

def NormalDensity.entropy (ρ : NormalDensity H) : ℝ≥0∞ := by
  classical
  exact if h : IsTraceClass ρ.entropyOperator then ENNReal.ofReal (traceNorm ρ.entropyOperator h) else ∞

theorem NormalDensity.entropy_ne_top_iff (ρ : NormalDensity H) :
    ρ.entropy ≠ ∞ ↔ IsTraceClass ρ.entropyOperator := by
  unfold NormalDensity.entropy
  split_ifs with h <;> simp [h]

theorem NormalDensity.entropy_eq_of_traceClass (ρ : NormalDensity H)
    (h : IsTraceClass ρ.entropyOperator) :
    ρ.entropy = ENNReal.ofReal (trace ρ.entropyOperator h).re := by
  classical
  rw [NormalDensity.entropy, dite_eq_left h]
  congr 1
  have hh := traceNorm_eq_re_trace_of_nonneg
    (TraceClass.ofOperator ρ.entropyOperator h) ρ.entropyOperator_nonneg
  simpa only [normalTrace_apply, TraceClass.ofOperator_coe] using hh

theorem NormalDensity.entropyOperator_conjugate (ρ : NormalDensity H)
    (U : unitary (H →L[ℂ] H)) :
    (ρ.conjugate U).entropyOperator =
      (U : H →L[ℂ] H) * ρ.entropyOperator * star (U : H →L[ℂ] H) := by
  have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U)
    Real.negMulLog ρ.operator.1 Real.continuous_negMulLog.continuousOn
    (by change Continuous (fun A : H →L[ℂ] H => (U : H →L[ℂ] H) * A * star (U : H →L[ℂ] H)); fun_prop)
    (IsSelfAdjoint.of_nonneg ρ.nonneg)
    (IsSelfAdjoint.of_nonneg (star_right_conjugate_nonneg ρ.nonneg (U : H →L[ℂ] H)))
  exact h.symm

lemma unitary_conjugate_inverse (A : H →L[ℂ] H) (U : unitary (H →L[ℂ] H)) :
    star (U : H →L[ℂ] H) * ((U : H →L[ℂ] H) * A * star (U : H →L[ℂ] H)) *
      (U : H →L[ℂ] H) = A := by
  calc
    _ = (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) * A *
      (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) := by simp only [mul_assoc]
    _ = A := by rw [Unitary.coe_star_mul_self, one_mul, mul_one]

theorem NormalDensity.entropyOperator_traceClass_conjugate_iff (ρ : NormalDensity H)
    (U : unitary (H →L[ℂ] H)) :
    IsTraceClass (ρ.conjugate U).entropyOperator ↔ IsTraceClass ρ.entropyOperator := by
  rw [ρ.entropyOperator_conjugate U]
  constructor
  · intro h
    have hi := isTraceClass_mul_mul (A := star (U : H →L[ℂ] H)) (B := (U : H →L[ℂ] H)) h
    rwa [unitary_conjugate_inverse] at hi
  · exact isTraceClass_mul_mul

theorem NormalDensity.entropy_conjugate (ρ : NormalDensity H)
    (U : unitary (H →L[ℂ] H)) : (ρ.conjugate U).entropy = ρ.entropy := by
  classical
  by_cases h : IsTraceClass ρ.entropyOperator
  · have hc := (ρ.entropyOperator_traceClass_conjugate_iff U).mpr h
    rw [(ρ.conjugate U).entropy_eq_of_traceClass hc, ρ.entropy_eq_of_traceClass h]
    congr 2
    exact (TraceClass.trace_transport (ρ.entropyOperator_conjugate U) hc).trans
      (trace_unitary_conjugate (TraceClass.ofOperator ρ.entropyOperator h) U)
  · have hc : ¬ IsTraceClass (ρ.conjugate U).entropyOperator :=
      fun hc => h ((ρ.entropyOperator_traceClass_conjugate_iff U).mp hc)
    simp only [NormalDensity.entropy, dite_eq_right h, dite_eq_right hc]

end Gaussian.Physical.Boson
