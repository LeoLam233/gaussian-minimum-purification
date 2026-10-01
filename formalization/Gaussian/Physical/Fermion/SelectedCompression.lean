import Gaussian.Physical.Fermion.PrefixCoefficient
import Gaussian.Physical.Fermion.CompressionBridge
import Gaussian.Physical.Fermion.GaussianClosure
import Gaussian.Phase.FrameExtension

set_option autoImplicit false
noncomputable section
open Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- A proved equality of actual trace covariance forms identifies the actual
reduced generator with orthogonal compression, with the left-slot sign explicit. -/
theorem covarianceGenerator_compression_of_form {n k : ℕ}
    (ρ : Density n) (σ : Density k) (V : Submodule ℝ (CoefficientSpace n))
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] V)
    (h : ∀ x y,covarianceForm σ x y = covarianceForm ρ (e x) (e y)) :
    ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) V (e x) := by
  intro x
  apply ext_inner_right ℝ
  intro y
  obtain ⟨z,rfl⟩ := e.surjective y
  calc
    ⟪e (covarianceGenerator σ x),e z⟫ = covarianceForm σ x z := by
      rw [e.inner_map_map,covarianceGenerator_inner]
    _ = covarianceForm ρ (e x) (e z) := h x z
    _ = ⟪covarianceGenerator ρ (e x),(e z : CoefficientSpace n)⟫ :=
      (covarianceGenerator_inner ρ _ _).symm
    _ = ⟪compression (covarianceGenerator ρ) V (e x),e z⟫ := by
      calc
        _ = ⟪(e z : CoefficientSpace n),covarianceGenerator ρ (e x)⟫ := real_inner_comm _ _
        _ = ⟪e z,compression (covarianceGenerator ρ) V (e x)⟫ :=
          (inner_compression V (e z) (e x)).symm
        _ = _ := real_inner_comm _ _

/-- The coefficient rows selected by a genuine CAR orthogonal transform followed
by complete-mode partial trace. -/
def selectedCoefficientEmbedding (k l : ℕ)
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k)) :
    CoefficientSpace k →ₗᵢ[ℝ] CoefficientSpace (l+k) :=
  R.symm.toLinearIsometry.comp (prefixCoefficientEmbedding k l)

/-- The actual state restriction has exactly the genuine selected compression. -/
theorem selectedRestriction_generator (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U) :
    ∀ x,(selectedCoefficientEmbedding k l R).equivRange
        (covarianceGenerator (prefixRestriction k l (ρ.uConj U)) x) =
      compression (covarianceGenerator ρ)
        (selectedCoefficientEmbedding k l R).toLinearMap.range
        ((selectedCoefficientEmbedding k l R).equivRange x) := by
  apply covarianceGenerator_compression_of_form
  intro x y
  exact orthogonalRestriction_covarianceForm k l ρ R U hU x y

/-- Every complete orthonormal CAR coefficient frame is physically realizable as
an actual unitary followed by actual complete-mode restriction. -/
theorem exists_restriction_with_frame (k l : ℕ) (ρ : Density (l+k))
    (hρ : IsQuasifree ρ) (f : CoefficientSpace k →ₗᵢ[ℝ] CoefficientSpace (l+k)) :
    ∃ R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k),
      ∃ U : Matrix.unitaryGroup (Occupation (l+k)) ℂ,
      Implements (l+k) R U ∧
      IsQuasifree (prefixRestriction k l (ρ.uConj U)) ∧
      ∀ x y,covarianceForm (prefixRestriction k l (ρ.uConj U)) x y =
        covarianceForm ρ (f x) (f y) := by
  obtain ⟨R,hR⟩ := exists_orthogonal_extension (prefixCoefficientEmbedding k l) f
  obtain ⟨U,hU⟩ := orthogonal_implemented (l+k) R
  refine ⟨R,U,hU,isQuasifree_orthogonalRestriction k l ρ hρ R U hU,?_⟩
  intro x y
  have hx : R⁻¹ (prefixCoefficientEmbedding k l x)=f x := by
    rw [← hR x]
    exact R.symm_apply_apply (f x)
  have hy : R⁻¹ (prefixCoefficientEmbedding k l y)=f y := by
    rw [← hR y]
    exact R.symm_apply_apply (f y)
  rw [orthogonalRestriction_covarianceForm k l ρ R U hU,hx,hy]

/-- The actual density entropy decreases for a genuinely selected J-invariant
CAR coefficient range; all implementation and spectrum bridges are discharged. -/
theorem selectedRestriction_entropy_le (k l : ℕ) (ρ : Density (l+k))
    (hρ : IsQuasifree ρ) (d : SkewAdaptationData (covarianceGenerator ρ))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (hJ : d.complexStructure.IsInvariant (selectedCoefficientEmbedding k l R).toLinearMap.range) :
    Sᵥₙ (prefixRestriction k l (ρ.uConj U)) ≤ Sᵥₙ ρ :=
  quasifree_entropy_comparison_of_compression ρ _ hρ
    (isQuasifree_orthogonalRestriction k l ρ hρ R U hU) d _ hJ
    (selectedCoefficientEmbedding k l R).equivRange
    (selectedRestriction_generator k l ρ R U hU)

end Gaussian.Physical.Fermion
