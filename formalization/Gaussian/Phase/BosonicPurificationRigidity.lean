import Gaussian.Phase.BosonicPurificationCompression
import Gaussian.Phase.BosonicPurificationCore

/-! Covariance-only C6 for the original two-form cost: genuine retained-form
comparison and exact pure discarded factors. Neither a prescribed spectrum nor
an actual density-state entropy identity is assumed. -/
noncomputable section
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
/-- Relabeling the finite index of the same genuine spectrum leaves its cost unchanged. -/
theorem realListCost_eigenvalues_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {K : F →ₗ[ℝ] F}
    (hK : K.IsSymmetric) (f : ℝ → ℝ) {n m : ℕ}
    (hn : finrank ℝ F = n) (hm : finrank ℝ F = m) :
    Gaussian.Entropy.realListCost f (hK.eigenvalues hn) =
      Gaussian.Entropy.realListCost f (hK.eigenvalues hm) := by
  subst n
  subst m
  rfl

namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

/-- Compression comparison for the independently defined cost of both actual forms. -/
theorem restricted_formCost_le (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U) :
    bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) ≤ bosonFormCost e V Ω d.covariance_symmetric hΩ := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have hn : finrank ℝ E = 2*n := by
    simp [Module.finrank_eq_card_basis e,mul_comm]
  have hm : finrank ℝ U = 2*m := by
    simp [Module.finrank_eq_card_basis eU,mul_comm]
  rw [d.formCost_eq_half_spectrum hΩ hLower hn e,
    d.restricted_formCost_eq_half_spectrum hΩ hLower U hU hm eU]
  have hle : 2*m ≤ 2*n := by simpa only [← hn,← hm] using U.finrank_le
  have hs : 2*m+(2*n-2*m) = 2*n := Nat.add_sub_of_le hle
  have hn' : finrank ℝ E = 2*m+(2*n-2*m) := hn.trans hs.symm
  have hc := Gaussian.Entropy.boson_compression_comparison
    (show d.K.IsSymmetric from d.amplitude_symm) (d.amplitude_sub_one_positive hLower) U hn' hm
  rwa [realListCost_eigenvalues_eq d.amplitude_symm Gaussian.Entropy.boson hn' hn] at hc

/-- Exact equality forces the endpoint on the whole true symplectic complement,
with the actual covariance cross block equal to zero. -/
theorem restricted_formCost_rigidity (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U)
    (he : bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) = bosonFormCost e V Ω d.covariance_symmetric hΩ) :
    (∀ x ∈ Ω.orthogonal U, d.K x = x) ∧
      (∀ x ∈ Ω.orthogonal U, ∀ y ∈ U, V x y = 0) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have hn : finrank ℝ E = 2*n := by simp [Module.finrank_eq_card_basis e,mul_comm]
  have hm : finrank ℝ U = 2*m := by simp [Module.finrank_eq_card_basis eU,mul_comm]
  rw [d.formCost_eq_half_spectrum hΩ hLower hn e,
    d.restricted_formCost_eq_half_spectrum hΩ hLower U hU hm eU] at he
  have hle : 2*m ≤ 2*n := by simpa only [← hn,← hm] using U.finrank_le
  have hs : 2*m+(2*n-2*m) = 2*n := Nat.add_sub_of_le hle
  have hn' : finrank ℝ E = 2*m+(2*n-2*m) := hn.trans hs.symm
  have he' : Gaussian.Entropy.realListCost Gaussian.Entropy.boson
      ((compression_symmetric (show d.K.IsSymmetric from d.amplitude_symm) U).eigenvalues hm) =
      Gaussian.Entropy.realListCost Gaussian.Entropy.boson
      ((show d.K.IsSymmetric from d.amplitude_symm).eigenvalues hn') := by
    exact he.trans (realListCost_eigenvalues_eq d.amplitude_symm Gaussian.Entropy.boson hn hn')
  have hr := Gaussian.Entropy.boson_compression_rigidity
    (show d.K.IsSymmetric from d.amplitude_symm) (d.amplitude_sub_one_positive hLower) U hn' hm he'
  have horth : Ω.orthogonal U = Uᗮ := by
    rw [← d.complexStructure_symplecticForm]
    exact d.complexStructure.symplectic_orthogonal_eq hU
  refine ⟨?_,?_⟩
  · simpa only [horth] using hr.1
  · intro x hx y hy
    rw [d.covariance_factor,d.metric_symm.eq]
    exact hr.2 x (horth ▸ hx) y hy

/-- The endpoint on an invariant factor constructs its actual pure covariance. -/
def pureRestrictionOfEndpoint (P : Submodule ℝ E) (hP : ∀ x ∈ P, d.J x ∈ P)
    (hK : ∀ x ∈ P, d.K x = x) : PureCompatibleCovariance (Ω.restrict P) where
  form := V.restrict P
  generator := d.J.restrict hP
  symmetric := d.covariance_symmetric.restrict P
  positive x hx := by
    change 0 < V x x
    rw [d.covariance_factor,hK x x.property]
    exact d.metric_pos x (fun h => hx (Subtype.ext h))
  square_neg x := by apply Subtype.ext; exact d.square_neg x
  compatible x y := by
    change V x y = Ω x (d.J y)
    rw [d.covariance_factor,hK y y.property,d.metric_eq]
  symplectic x y := d.symplectic_isometry x y

@[simp] theorem pureRestrictionOfEndpoint_form (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, d.J x ∈ P) (hK : ∀ x ∈ P, d.K x = x) (x y : P) :
    (d.pureRestrictionOfEndpoint P hP hK).form x y = V x y := rfl

/-- Equality in the independently defined covariance cost produces an actual
pure covariance on the entire discarded symplectic factor. -/
theorem exists_pure_discarded_of_formCost_eq (hΩ : Ω.IsAlt)
    (hLower : ∀ x, d.g x x ≤ V x x) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U)
    (he : bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) = bosonFormCost e V Ω d.covariance_symmetric hΩ) :
    ∃ p : PureCompatibleCovariance (Ω.restrict (Ω.orthogonal U)),
      p.form = V.restrict (Ω.orthogonal U) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have horth : Ω.orthogonal U = Uᗮ := by
    rw [← d.complexStructure_symplecticForm]
    exact d.complexStructure.symplectic_orthogonal_eq hU
  have hP : ∀ x ∈ Ω.orthogonal U, d.J x ∈ Ω.orthogonal U := by
    rw [horth]
    exact d.complexStructure.orthogonal_invariant hU
  exact ⟨d.pureRestrictionOfEndpoint (Ω.orthogonal U) hP
    (d.restricted_formCost_rigidity hΩ hLower U hU e eU he).1,rfl⟩

end BosonicAdaptationData
end Gaussian.Phase
