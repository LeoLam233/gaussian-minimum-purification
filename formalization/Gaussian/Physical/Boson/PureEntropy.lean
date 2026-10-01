import Gaussian.Physical.Boson.NormalEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-! Actual pure normal densities have zero extended von Neumann entropy,
without a finite-dimensional Hilbert-space assumption. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorDensity_entropyOperator (x : H) (hx : ‖x‖ = 1) :
    (vectorDensity x hx).entropyOperator = 0 := by
  have hp := InnerProductSpace.isIdempotentElem_rankOne_self (𝕜 := ℂ) hx
  have hs : spectrum ℝ (InnerProductSpace.rankOne ℂ x x) ⊆ {0,1} :=
    (isIdempotentElem_iff_spectrum_subset ℝ _
      (IsSelfAdjoint.of_nonneg (vectorDensity x hx).nonneg)).mp hp
  change cfc Real.negMulLog (InnerProductSpace.rankOne ℂ x x) = 0
  rw [← cfc_zero ℝ (InnerProductSpace.rankOne ℂ x x)]
  apply cfc_congr
  intro t ht
  have h := hs ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl <;> simp

theorem vectorDensity_entropy (x : H) (hx : ‖x‖ = 1) : (vectorDensity x hx).entropy = 0 := by
  have ht : IsTraceClass (vectorDensity x hx).entropyOperator := by
    rw [vectorDensity_entropyOperator]
    exact isTraceClass_zero
  rw [NormalDensity.entropy, dite_eq_left ht]
  simp only [vectorDensity_entropyOperator, traceNorm_zero, ENNReal.ofReal_zero]

theorem NormalDensity.IsPure.entropy_eq_zero {ρ : NormalDensity H} (hρ : ρ.IsPure) :
    ρ.entropy = 0 := by
  obtain ⟨x,hx,rfl⟩ := hρ
  exact vectorDensity_entropy x hx

end Gaussian.Physical.Boson
