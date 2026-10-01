import Gaussian.Phase.PairedFrame

/-! An actual simultaneous canonical/diagonal basis for the original covariance
and commutator forms. This coefficient-level Williamson theorem does not assert
realization as a Gaussian density state or its von Neumann entropy. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

/-- An actual g-orthonormal, J-canonical eigenbasis of the constructed amplitude. -/
def pairedFrame {n : ℕ} (hn : finrank ℝ E = 2*n) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    PairedEigenframe d.complexStructure d.K n := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  exact Classical.choice (exists_pairedEigenframe_dim n E hn d.complexStructure d.K
    (show d.K.IsSymmetric from d.amplitude_symm) d.commute)

/-- The original commutator is exactly canonical in the constructed basis. -/
theorem pairedFrame_commutator {n : ℕ} (hn : finrank ℝ E = 2*n) (i j : Fin n × Fin 2) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    Ω ((d.pairedFrame hn).basis i) ((d.pairedFrame hn).basis j) = canonicalModeMatrix n i j := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have h := (d.pairedFrame hn).symplectic_matrix i j
  rw [d.complexStructure_symplecticForm] at h
  exact h

/-- The original covariance is paired diagonal in the same basis. -/
theorem pairedFrame_covariance {n : ℕ} (hn : finrank ℝ E = 2*n) (i j : Fin n × Fin 2) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    V ((d.pairedFrame hn).basis i) ((d.pairedFrame hn).basis j) =
      if i=j then (d.pairedFrame hn).value i.1 else 0 := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  rw [d.covariance_factor]
  exact (d.pairedFrame hn).amplitude_matrix i j

/-- Uncertainty lower endpoints hold for the actual Williamson parameters. -/
theorem pairedFrame_value_ge_one (hLower : ∀ x, d.g x x ≤ V x x)
    {n : ℕ} (hn : finrank ℝ E = 2*n) (i : Fin n) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    1 ≤ (d.pairedFrame hn).value i := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  apply (d.pairedFrame hn).value_ge 1 _ i
  intro x
  change 1*d.g x x ≤ d.g x (d.K x)
  rw [one_mul,← d.covariance_factor]
  exact hLower x

/-- The half-weighted real spectral sum is precisely the once-per-Williamson-mode sum. -/
theorem pairedFrame_half_spectral_sum {n : ℕ} (hn : finrank ℝ E = 2*n) (f : ℝ → ℝ) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    (1/2:ℝ) * (∑ i : Fin (2*n), f ((show d.K.IsSymmetric from d.amplitude_symm).eigenvalues hn i)) =
      ∑ i : Fin n, f ((d.pairedFrame hn).value i) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  exact paired_half_spectral_sum (d.pairedFrame hn) d.amplitude_symm f

end BosonicAdaptationData

/-- Raw finite-dimensional coefficient Williamson theorem. The basis is
invertible and sends BOTH original forms to their true canonical/paired-diagonal
forms. Pure endpoints, degeneracies, zero modes of the ambient system, and
arbitrarily large finite covariance parameters are included. -/
theorem exists_williamson_basis {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (V Ω : LinearMap.BilinForm ℝ E)
    (hVs : V.IsSymm) (hVp : ∀ x, x ≠ 0 → 0 < V x x)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate) {n : ℕ} (hn : finrank ℝ E = 2*n)
    (hUnc : ∀ x y, (Ω x y)^2 ≤ V x x * V y y) :
    ∃ (ν : Fin n → ℝ) (b : Basis (Fin n × Fin 2) ℝ E),
      (∀ i, 1 ≤ ν i) ∧
      (∀ i j, Ω (b i) (b j) = canonicalModeMatrix n i j) ∧
      (∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0) := by
  obtain ⟨d,hLower⟩ := exists_bosonicAdaptation V Ω hVs hVp hΩa hΩn (by
    refine ⟨n,?_⟩
    omega) hUnc
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  refine ⟨(d.pairedFrame hn).value,(d.pairedFrame hn).basis.toBasis,?_,?_,?_⟩
  · exact d.pairedFrame_value_ge_one hLower hn
  · exact d.pairedFrame_commutator hn
  · exact d.pairedFrame_covariance hn

end Gaussian.Phase
