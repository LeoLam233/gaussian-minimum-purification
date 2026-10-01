import Gaussian.Phase.BosonicPurificationCost

/-! The independently defined cost of both genuinely restricted bosonic forms
is the half-spectrum of the actual adapted-metric orthogonal compression.
The comparison and equality conclusions are covariance-only statements. -/
noncomputable section
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

/-- The original Hermitian-pair cost equals the actual adapted amplitude cost. -/
theorem formCost_eq_half_spectrum (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    {n : ℕ} (hn : finrank ℝ E = 2*n) (e : Basis (Fin n × Bool) ℝ E) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    bosonFormCost e V Ω d.covariance_symmetric hΩ =
      Gaussian.Entropy.realListCost Gaussian.Entropy.boson
        ((show d.K.IsSymmetric from d.amplitude_symm).eigenvalues hn) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  apply (d.pairedFrame hn).formCost_eq_half_spectrum e V Ω d.covariance_symmetric hΩ
    d.covariance_factor _ (d.pairedFrame_value_ge_one hLower hn) d.amplitude_symm hn
  intro x y
  exact (congrArg (fun B : LinearMap.BilinForm ℝ E => B x y)
    d.complexStructure_symplecticForm).symm

/-- Both restricted forms determine precisely the genuine compression spectrum.
The retained subspace need only be J-invariant, not K-invariant. -/
theorem restricted_formCost_eq_half_spectrum (hΩ : Ω.IsAlt)
    (hLower : ∀ x, d.g x x ≤ V x x) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) {m : ℕ} (hm : finrank ℝ U = 2*m)
    (e : Basis (Fin m × Bool) ℝ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    bosonFormCost e (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) =
      Gaussian.Entropy.realListCost Gaussian.Entropy.boson
        ((compression_symmetric (show d.K.IsSymmetric from d.amplitude_symm) U).eigenvalues hm) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  let JU := d.complexStructure.restrict U hU
  let KU := compression d.K U
  have hKU : KU.IsSymmetric := compression_symmetric d.amplitude_symm U
  have hcomm : ∀ x, JU (KU x) = KU (JU x) :=
    d.complexStructure.compression_commute U hU d.K d.commute
  obtain ⟨b⟩ := exists_pairedEigenframe_dim m U hm JU KU hKU hcomm
  have hν : ∀ i, 1 ≤ b.value i := by
    apply b.value_ge 1
    intro x
    simpa only [real_inner_self_eq_norm_sq] using
      compression_lower_quadratic U 1 (lower_quadratic_of_defect
        (d.amplitude_sub_one_positive hLower)) x
  apply b.formCost_eq_half_spectrum e (V.restrict U) (Ω.restrict U)
    (d.covariance_symmetric.restrict U) (fun x => hΩ x) _ _ hν hKU hm
  · intro x y
    change V x y = ⟪x,compression d.K U y⟫
    rw [inner_compression]
    exact d.covariance_factor x y
  · intro x y
    change Ω x y = -d.g x (d.J y)
    rw [d.metric_eq,d.square_neg,map_neg,neg_neg]

end BosonicAdaptationData
end Gaussian.Phase
