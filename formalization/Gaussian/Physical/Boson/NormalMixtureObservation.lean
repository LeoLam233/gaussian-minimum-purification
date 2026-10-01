import Gaussian.Physical.Boson.Observation

/-! Actual bounded-observable expectations of countable or arbitrary-index normal mixtures,
with a proved HasSum inherited from trace-norm convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped InnerProductSpace
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hasSum_normalMixture_expect (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : HasSum p 1) (v : ι → H) (hv : ∀ i, ‖v i‖=1) (A : H →L[ℂ] H) :
    HasSum (fun i => (p i : ℂ)*⟪v i,A (v i)⟫_ℂ) ((normalMixture p hp hs v hv).expect A) := by
  have h := (summable_weighted_vectorOperator p hp hs.summable v hv).hasSum.mapL
    (TraceClass.tracePairing A)
  have he (i : ι) : TraceClass.tracePairing A ((p i : ℂ) • vectorOperator (v i)) =
      (p i : ℂ)*⟪v i,A (v i)⟫_ℂ := by
    rw [map_smul]
    change (p i : ℂ)*((vectorDensity (v i) (hv i)).expect A)=_
    rw [vectorDensity_expect]
  change HasSum (fun i => (p i : ℂ)*⟪v i,A (v i)⟫_ℂ)
    (TraceClass.tracePairing A (∑' i, (p i : ℂ) • vectorOperator (v i)))
  simpa only [he] using h

end Gaussian.Physical.Boson
