import Gaussian.Physical.Boson.NuclearExpansion

/-! Countable absolutely nuclear expansions of genuine trace-class operators.
Countability is derived from the finite trace norm, not assumed for the Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_countable_nuclear_expansion (T : TraceClass H) :
    ∃ (ι : Type u) (_ : Countable ι) (a b : ι → H),
      Summable (fun i => ‖a i‖ * ‖b i‖) ∧ T = ∑' i, outerOperator (a i) (b i) := by
  obtain ⟨w,e,_⟩ := exists_hilbertBasis ℂ H
  let R := Polar.polarFactor T.1 * CFC.sqrt (CFC.abs T.1)
  let S := CFC.sqrt (CFC.abs T.1)
  obtain ⟨hR,hS,_⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs T.2
  have hs : Summable (fun i : w => ‖R (e i)‖ * ‖S (e i)‖) := by
    simpa only [norm_outerOperator] using summable_norm_outer_basis e R S hR hS
  let s := Function.support (fun i : w => ‖R (e i)‖ * ‖S (e i)‖)
  have hc : s.Countable := hs.countable_support
  refine ⟨s, hc.to_subtype, (fun i => R (e i.1)), (fun i => S (e i.1)), hs.subtype s, ?_⟩
  rw [traceClass_eq_nuclearBasisSeries T e]
  change (∑' i : w, outerOperator (R (e i)) (S (e i))) = _
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun i : w => outerOperator (R (e i)) (S (e i))) (s := s)
  intro i hi
  change ‖R (e i)‖ * ‖S (e i)‖ ≠ 0
  rw [← norm_outerOperator]
  exact norm_ne_zero_iff.mpr hi

end Gaussian.Physical.Boson
