import Gaussian.Physical.Boson.RankOneContinuity

/-! Genuine trace-class nuclear expansions from the qualified Hilbert–Schmidt factorization.
This supplies an explicit analytic interface for Weyl-characteristic injectivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma summable_norm_outer_basis {w : Set H} (b : HilbertBasis w ℂ H)
    (R S : H →L[ℂ] H) (hR : HilbertSchmidt.IsHilbertSchmidt R) (hS : HilbertSchmidt.IsHilbertSchmidt S) :
    Summable (fun i : w => ‖outerOperator (R (b i)) (S (b i))‖) := by
  simp only [norm_outerOperator]
  exact HilbertSchmidt.summable_norm_mul_of_square_sums
    (fun i : w => ‖R (b i)‖) (fun i : w => ‖S (b i)‖)
    (HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hR)
    (HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

def nuclearBasisSeries {w : Set H} (b : HilbertBasis w ℂ H) (R S : H →L[ℂ] H) : TraceClass H :=
  ∑' i : w, outerOperator (R (b i)) (S (b i))

/-- The trace-norm convergent outer-product series represents the actual bounded product RS*. -/
theorem nuclearBasisSeries_apply {w : Set H} (b : HilbertBasis w ℂ H)
    (R S : H →L[ℂ] H) (hR : HilbertSchmidt.IsHilbertSchmidt R) (hS : HilbertSchmidt.IsHilbertSchmidt S) (x : H) :
    (nuclearBasisSeries b R S).1 x = R (star S x) := by
  let ev : TraceClass H →L[ℂ] H := (ContinuousLinearMap.apply ℂ H x).comp traceClassInclusion
  have hsum := (summable_norm_outer_basis b R S hR hS).of_norm.hasSum.mapL ev
  have hcoeff : ∀ i : w, ev (outerOperator (R (b i)) (S (b i))) =
      R (b.repr (star S x) i • b i) := by
    intro i
    change ⟪S (b i),x⟫_ℂ • R (b i) = _
    rw [map_smul, HilbertBasis.repr_apply_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hparseval := (b.hasSum_repr (star S x)).mapL R
  have hsecond : HasSum (fun i : w => ev (outerOperator (R (b i)) (S (b i)))) (R (star S x)) := by
    simpa only [hcoeff] using hparseval
  exact hsum.unique hsecond

/-- Every trace-class operator has an explicit absolutely trace-norm-convergent nuclear expansion. -/
theorem traceClass_eq_nuclearBasisSeries (T : TraceClass H) {w : Set H} (b : HilbertBasis w ℂ H) :
    T = nuclearBasisSeries b
      (Polar.polarFactor T.1 * CFC.sqrt (CFC.abs T.1)) (CFC.sqrt (CFC.abs T.1)) := by
  obtain ⟨hR,hS,hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs T.2
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rw [nuclearBasisSeries_apply b _ _ hR hS]
  have hself : IsSelfAdjoint (CFC.sqrt (CFC.abs T.1)) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  rw [hself.star_eq]
  exact (congrArg (fun A : H →L[ℂ] H => A x) hfactor).symm

end Gaussian.Physical.Boson
