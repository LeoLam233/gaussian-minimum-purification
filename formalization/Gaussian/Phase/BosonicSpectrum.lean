import Gaussian.Phase.SpectralPairing

/-! A metric spectral bridge for the original generalized restricted operator.
This alone is not called Williamson normal form; a canonical paired eigenframe
is constructed separately. -/
noncomputable section
open Module
namespace Gaussian.Phase.BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

theorem restricted_singularValues (hVp : ∀ x, x ≠ 0 → 0 < V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U)
    {n : ℕ} (hn : finrank ℝ U = n) (i : Fin n) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    (rightFormGenerator (V.restrict U) (Ω.restrict U)
      (d.restricted_commutator_nondegenerate U hU)).singularValues i =
      (compression_positive d.K (d.amplitude_positive hVp) U).isSymmetric.eigenvalues hn i := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  exact singularValues_eq_amplitude (d.complexStructure.restrict U hU)
    (rightFormGenerator (V.restrict U) (Ω.restrict U)
      (d.restricted_commutator_nondegenerate U hU)) (Gaussian.Spectral.compression d.K U)
    (compression_positive d.K (d.amplitude_positive hVp) U)
    (d.restricted_right_generator U hU) hn i

/-- Even multiplicities for the actual generalized pair's real singular list
in its proved compatible metric. -/
theorem restricted_even_multiplicity (hVp : ∀ x, x ≠ 0 → 0 < V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U)
    {n : ℕ} (hn : finrank ℝ U = n) (a : ℝ) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    Even (Finset.card {i : Fin n | (rightFormGenerator (V.restrict U) (Ω.restrict U)
      (d.restricted_commutator_nondegenerate U hU)).singularValues i = a}) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  simp_rw [d.restricted_singularValues hVp U hU hn]
  exact (d.complexStructure.restrict U hU).even_eigenvalue_multiplicity _
    (compression_positive d.K (d.amplitude_positive hVp) U).isSymmetric
    (d.complexStructure.compression_commute U hU d.K d.commute) hn a

end Gaussian.Phase.BosonicAdaptationData
