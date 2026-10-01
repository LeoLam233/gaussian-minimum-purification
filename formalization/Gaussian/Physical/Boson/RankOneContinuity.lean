import Gaussian.Physical.Boson.ProbabilityMixture

/-! Trace-norm continuity of genuine vector density operators.
The Hilbert space may be infinite dimensional. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma rankOne_factor (x y : H) (hx : x ≠ 0) :
    ((‖x‖^2 : ℝ) : ℂ)⁻¹ •
      (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y) =
      InnerProductSpace.rankOne ℂ x y := by
  have hn : ((‖x‖^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hi : ⟪x,x⟫_ℂ = ((‖x‖^2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne,
    hi, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Every mixed rank-one operator is genuinely trace class. -/
theorem isTraceClass_rankOne (x y : H) : IsTraceClass (InnerProductSpace.rankOne ℂ x y) := by
  by_cases hx : x = 0
  · subst x
    simpa using (isTraceClass_zero (H := H))
  have hp : IsTraceClass (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y) := by
    simpa only [one_mul] using isTraceClass_mul_mul (A := 1)
      (B := InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne_self x)
  rw [← rankOne_factor x y hx]
  exact isTraceClass_smul _ hp

/-- Rank-one operators bundled in the trace-norm Banach space. -/
def outerOperator (x y : H) : TraceClass H :=
  TraceClass.ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y)

@[simp] theorem outerOperator_coe (x y : H) :
    (outerOperator x y).1 = InnerProductSpace.rankOne ℂ x y := rfl

/-- The trace norm of a rank-one operator is the product of vector norms. -/
theorem norm_outerOperator (x y : H) : ‖outerOperator x y‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm
  · by_cases hx : x = 0
    · subst x
      have he : outerOperator (0:H) y = 0 := by
        apply Subtype.ext
        change InnerProductSpace.rankOne ℂ (0:H) y = 0
        simp
      rw [he]; simp
    have hp : IsTraceClass (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y) := by
      simpa only [one_mul] using isTraceClass_mul_mul (A := 1)
        (B := InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne_self x)
    have hbound := traceNorm_mul_mul_le (A := (1 : H →L[ℂ] H))
      (B := InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne_self x) hp
    simp only [one_mul, traceNorm_rankOne_self, InnerProductSpace.norm_rankOne] at hbound
    have hbound' : traceNorm (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y) hp ≤
        ‖x‖^2 * (‖x‖ * ‖y‖) := by
      calc
        _ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖x‖^2 * (‖x‖ * ‖y‖) := hbound
        _ ≤ 1 * ‖x‖^2 * (‖x‖ * ‖y‖) := by gcongr; exact ContinuousLinearMap.norm_id_le
        _ = _ := by ring
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    calc
      ‖outerOperator x y‖ = traceNorm (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y) := rfl
      _ = traceNorm (((‖x‖^2 : ℝ) : ℂ)⁻¹ •
          (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y)) _ :=
        traceNorm_transport (rankOne_factor x y hx).symm _
      _ = ‖((‖x‖^2 : ℝ) : ℂ)⁻¹‖ *
          traceNorm (InnerProductSpace.rankOne ℂ x x * InnerProductSpace.rankOne ℂ x y) hp :=
        traceNorm_smul _ hp
      _ ≤ ‖((‖x‖^2 : ℝ) : ℂ)⁻¹‖ * (‖x‖^2 * (‖x‖ * ‖y‖)) :=
        mul_le_mul_of_nonneg_left hbound' (norm_nonneg _)
      _ = ‖x‖ * ‖y‖ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        field_simp
  · calc
      ‖x‖ * ‖y‖ = ‖(outerOperator x y).1‖ := (InnerProductSpace.norm_rankOne x y).symm
      _ ≤ ‖outerOperator x y‖ := opNorm_le_traceNorm (outerOperator x y).2

lemma vectorOperator_sub (x y : H) :
    vectorOperator x - vectorOperator y = outerOperator (x-y) x + outerOperator y (x-y) := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x x - InnerProductSpace.rankOne ℂ y y =
    InnerProductSpace.rankOne ℂ (x-y) x + InnerProductSpace.rankOne ℂ y (x-y)
  ext z
  simp only [sub_apply, add_apply, InnerProductSpace.rankOne_apply,
    inner_sub_left, sub_smul, smul_sub]
  abel

/-- Trace-norm control, not merely operator-norm continuity. -/
theorem norm_vectorOperator_sub_le (x y : H) :
    ‖vectorOperator x - vectorOperator y‖ ≤ (‖x‖ + ‖y‖) * ‖x-y‖ := by
  rw [vectorOperator_sub]
  calc
    _ ≤ ‖outerOperator (x-y) x‖ + ‖outerOperator y (x-y)‖ := norm_add_le _ _
    _ = _ := by rw [norm_outerOperator, norm_outerOperator]; ring

/-- The vector-state map is continuous for the trace norm, not just weak or operator topology. -/
theorem continuous_vectorOperator : Continuous (vectorOperator : H → TraceClass H) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun y => norm_nonneg _) (fun y => norm_vectorOperator_sub_le y x)
  have h : Continuous (fun y : H => (‖y‖ + ‖x‖) * ‖y-x‖) := by fun_prop
  simpa only [sub_self, norm_zero, mul_zero] using h.tendsto x

end Gaussian.Physical.Boson
