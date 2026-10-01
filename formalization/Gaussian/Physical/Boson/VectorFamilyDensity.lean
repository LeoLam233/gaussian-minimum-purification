import Gaussian.Physical.Boson.NuclearExpansion

/-! Actual positive trace-norm mixtures of unnormalized vectors. This is an
analytic construction for normal reductions; no marginal interpretation is
assumed in its inputs. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem summable_vectorOperator {ι : Type*} (v : ι → H)
    (hv : Summable (fun i => ‖v i‖^2)) : Summable (fun i => vectorOperator (v i)) := by
  apply Summable.of_norm
  simpa only [norm_vectorOperator] using hv

def normalVectorFamily {ι : Type*} (v : ι → H)
    (hv : HasSum (fun i => ‖v i‖^2) 1) : NormalDensity H where
  operator := ∑' i,vectorOperator (v i)
  nonneg := by
    have hc := traceClassInclusion.map_tsum (summable_vectorOperator v hv.summable)
    rw [traceClassInclusion_apply] at hc
    rw [hc]
    exact tsum_nonneg (fun i => (InnerProductSpace.rankOne ℂ (v i) (v i)).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self (v i)))
  trace_one := by
    rw [normalTrace.map_tsum (summable_vectorOperator v hv.summable)]
    simpa only [normalTrace_vectorOperator,Complex.ofReal_one] using (Complex.hasSum_ofReal.mpr hv).tsum_eq

theorem vectorOperator_pairing (x : H) (A : H →L[ℂ] H) :
    TraceClass.tracePairing A (vectorOperator x)=⟪x,A x⟫_ℂ := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
  rw [TraceClass.tracePairing_apply,trace_eq_of_hilbertBasis _ b]
  simpa only [vectorOperator_coe,mul_apply_eq_comp,InnerProductSpace.rankOne_apply,
    map_smul,inner_smul_right] using b.tsum_inner_mul_inner x (A x)

theorem normalVectorFamily_expect {ι : Type*} (v : ι → H)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (A : H →L[ℂ] H) :
    (normalVectorFamily v hv).expect A=∑' i,⟪v i,A (v i)⟫_ℂ := by
  change TraceClass.tracePairing A (∑' i,vectorOperator (v i)) = _
  rw [(TraceClass.tracePairing A).map_tsum (summable_vectorOperator v hv.summable)]
  simp only [vectorOperator_pairing]

theorem NormalDensity.sqrt_isHilbertSchmidt (ρ : NormalDensity H) :
    HilbertSchmidt.IsHilbertSchmidt (CFC.sqrt ρ.operator.1) := by
  simpa only [CFC.abs_of_nonneg _ ρ.nonneg] using
    isHilbertSchmidt_sqrt_abs_of_isTraceClass ρ.operator.2

theorem NormalDensity.sqrt_vector_series (ρ : NormalDensity H)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w,vectorOperator ((CFC.sqrt ρ.operator.1) (b i)))=ρ.operator := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change (nuclearBasisSeries b (CFC.sqrt ρ.operator.1) (CFC.sqrt ρ.operator.1)).1 x=ρ.operator.1 x
  rw [nuclearBasisSeries_apply b _ _ ρ.sqrt_isHilbertSchmidt ρ.sqrt_isHilbertSchmidt]
  have hs : IsSelfAdjoint (CFC.sqrt ρ.operator.1) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  rw [hs.star_eq]
  change (CFC.sqrt ρ.operator.1 * CFC.sqrt ρ.operator.1) x=ρ.operator.1 x
  rw [CFC.sqrt_mul_sqrt_self _ ρ.nonneg]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem NormalDensity.sqrt_vectors_hasSum (ρ : NormalDensity H)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    HasSum (fun i : w => ‖(CFC.sqrt ρ.operator.1) (b i)‖^2) 1 := by
  have hs := HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b ρ.sqrt_isHilbertSchmidt
  have hc := (summable_vectorOperator (fun i : w => (CFC.sqrt ρ.operator.1) (b i)) hs).hasSum.mapL normalTrace
  rw [ρ.sqrt_vector_series b,ρ.trace_one] at hc
  have hc' : HasSum (fun i : w => ((‖(CFC.sqrt ρ.operator.1) (b i)‖^2 : ℝ) : ℂ)) 1 := by
    simpa only [normalTrace_vectorOperator] using hc
  exact Complex.hasSum_ofReal.mp (by simpa only [Complex.ofReal_one] using hc')

theorem NormalDensity.eq_normalVectorFamily_sqrt (ρ : NormalDensity H)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    ρ=normalVectorFamily (fun i : w => (CFC.sqrt ρ.operator.1) (b i)) (ρ.sqrt_vectors_hasSum b) := by
  apply NormalDensity.ext
  exact (ρ.sqrt_vector_series b).symm

end Gaussian.Physical.Boson
