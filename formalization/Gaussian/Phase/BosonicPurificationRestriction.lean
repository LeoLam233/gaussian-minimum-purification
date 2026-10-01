import Gaussian.Phase.BosonicPurificationCore
import Gaussian.Phase.PureCompression

/-! Covariance-only decoupling of a pure restricted bosonic pair. The ambient
pure covariance supplies the metric; local mixed-cut invariance is not assumed. -/
noncomputable section
open Module
open Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {Ω : LinearMap.BilinForm ℝ E} (d : PureCompatibleCovariance Ω)

/-- The actual ambient pure covariance, used as the Hilbert metric. -/
@[instance_reducible] def metricCore : InnerProductSpace.Core ℝ E :=
  covarianceInnerCore d.form d.symmetric d.positive

/-- The actual ambient pure generator is orthogonal for its covariance metric. -/
def complexStructure :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    OrthogonalComplexStructure E := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  exact {
    equiv := LinearIsometryEquiv.ofSurjective
      { toLinearMap := d.generator
        norm_map' := fun x => by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            ← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
          exact d.metric_isometry x x }
      (fun x => ⟨-d.generator x,by simp [d.square_neg]⟩)
    square_neg := d.square_neg }

/-- The symplectic form recovered from the covariance metric is the original Ω. -/
theorem complexStructure_symplecticForm :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    d.complexStructure.symplecticForm = Ω := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  ext x y
  change -d.form x (d.generator y) = Ω x y
  rw [d.compatible,d.square_neg,map_neg,neg_neg]

/-- If the actual restricted pair is pure, its generator equals the actual
ambient covariance-metric compression. No ambient invariance is presupposed. -/
theorem pure_restriction_generator_eq_compression (P : Submodule ℝ E)
    (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    compression d.generator P = Jp := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  change ⟪x,P.orthogonalProjectionOnto (d.generator y)⟫ = ⟪x,Jp y⟫
  rw [P.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change d.form x (d.generator y) = d.form x (Jp y)
  calc
    _ = -Ω x y := by rw [d.compatible,d.square_neg,map_neg]
    _ = _ := by
      have h := hcompat x (Jp y)
      simpa only [hsq,Submodule.coe_neg,map_neg] using h.symm

/-- Covariance purity of an actual restricted pair forces global invariance. -/
theorem pure_restriction_invariant (P : Submodule ℝ E)
    (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) :
    ∀ x ∈ P, d.generator x ∈ P := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  apply d.complexStructure.invariant_of_pure_compression P
  intro x
  change compression d.generator P (compression d.generator P x) = -x
  rw [d.pure_restriction_generator_eq_compression P Jp hsq hcompat]
  exact hsq x

/-- The selected pure subspace and its true Ω-complement split the ambient
covariance, with nondegenerate restricted forms and vanishing cross covariance. -/
theorem pure_restriction_split (P : Submodule ℝ E)
    (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) :
    (∀ x ∈ P, d.generator x ∈ P) ∧
    (∀ x ∈ Ω.orthogonal P, d.generator x ∈ Ω.orthogonal P) ∧
    IsCompl P (Ω.orthogonal P) ∧ (Ω.restrict P).Nondegenerate ∧
    (Ω.restrict (Ω.orthogonal P)).Nondegenerate ∧
    (∀ x ∈ P, ∀ y ∈ Ω.orthogonal P, d.form x y = 0) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have hP : d.complexStructure.IsInvariant P := d.pure_restriction_invariant P Jp hsq hcompat
  have hQ := d.complexStructure.orthogonal_invariant hP
  have hΩP : Ω.orthogonal P = Pᗮ := by
    rw [← d.complexStructure_symplecticForm]
    exact d.complexStructure.symplectic_orthogonal_eq hP
  have hQ' : ∀ x ∈ Ω.orthogonal P, d.generator x ∈ Ω.orthogonal P := by
    rw [hΩP]
    exact hQ
  refine ⟨hP,hQ',?_,?_,?_,?_⟩
  · rw [hΩP]
    exact P.isCompl_orthogonal
  · rw [← d.complexStructure_symplecticForm]
    exact d.complexStructure.symplectic_restrict_nondegenerate hP
  · rw [hΩP,← d.complexStructure_symplecticForm]
    exact d.complexStructure.symplectic_restrict_nondegenerate hQ
  · intro x hx y hy
    rw [d.compatible]
    exact hQ' y hy x hx

end PureCompatibleCovariance
end Gaussian.Phase
