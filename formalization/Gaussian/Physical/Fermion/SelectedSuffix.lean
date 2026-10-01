import Gaussian.Physical.Fermion.SuffixCoefficient
import Gaussian.Physical.Fermion.CoefficientSplit
import Gaussian.Physical.Fermion.SelectedCompression
import Gaussian.Physical.Fermion.CompressionRigidity

set_option autoImplicit false
noncomputable section
open Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def selectedSuffixEmbedding (k l : ℕ)
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k)) :
    CoefficientSpace l →ₗᵢ[ℝ] CoefficientSpace (l+k) :=
  R.symm.toLinearIsometry.comp (suffixCoefficientEmbedding k l)

theorem selected_suffix_range_eq_prefix_orthogonal (k l : ℕ)
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k)) :
    (selectedSuffixEmbedding k l R).toLinearMap.range =
      (selectedCoefficientEmbedding k l R).toLinearMap.rangeᗮ := by
  change (R.symm.toLinearEquiv.toLinearMap.comp (suffixCoefficientEmbedding k l).toLinearMap).range =
    (R.symm.toLinearEquiv.toLinearMap.comp (prefixCoefficientEmbedding k l).toLinearMap).rangeᗮ
  rw [LinearMap.range_comp,LinearMap.range_comp,suffix_range_eq_prefix_orthogonal,
    Submodule.map_orthogonal_equiv]

theorem selectedSuffix_generator (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U) :
    ∀ x,(selectedSuffixEmbedding k l R).equivRange
        (covarianceGenerator (suffixRestriction k l (ρ.uConj U)) x) =
      compression (covarianceGenerator ρ)
        (selectedSuffixEmbedding k l R).toLinearMap.range
        ((selectedSuffixEmbedding k l R).equivRange x) := by
  apply covarianceGenerator_compression_of_form
  intro x y
  exact orthogonalSuffixRestriction_covarianceForm k l ρ R U hU x y

/-- Exact entropy equality in an adapted actual prefix cut forces the actual
complementary CAR marginal to be pure. This is the selected-deletion bridge. -/
theorem selectedSuffix_pure_of_entropy_eq (k l : ℕ) (ρ : Density (l+k))
    (hρ : IsQuasifree ρ) (d : SkewAdaptationData (covarianceGenerator ρ))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (hJ : d.complexStructure.IsInvariant (selectedCoefficientEmbedding k l R).toLinearMap.range)
    (he : Sᵥₙ (prefixRestriction k l (ρ.uConj U))=Sᵥₙ ρ) :
    ∃ ψ,suffixRestriction k l (ρ.uConj U)=MState.pure ψ := by
  have hpre := isQuasifree_orthogonalRestriction k l ρ hρ R U hU
  have hsuf := isQuasifree_suffixRestriction k l (ρ.uConj U)
    (isQuasifree_unitary_of_implements (l+k) ρ hρ R U hU)
  have hr := quasifree_compression_entropy_rigidity ρ _ hρ hpre d _ hJ
    (selectedCoefficientEmbedding k l R).equivRange (selectedRestriction_generator k l ρ R U hU) he
  have hS : d.complexStructure.IsInvariant (selectedSuffixEmbedding k l R).toLinearMap.range := by
    rw [selected_suffix_range_eq_prefix_orthogonal]
    exact d.complexStructure.orthogonal_invariant hJ
  apply quasifree_pure_of_adapted_endpoint ρ _ hsuf d _ hS
    (selectedSuffixEmbedding k l R).equivRange (selectedSuffix_generator k l ρ R U hU)
  intro x hx
  exact hr.1 x ((selected_suffix_range_eq_prefix_orthogonal k l R) ▸ hx)

end Gaussian.Physical.Fermion
