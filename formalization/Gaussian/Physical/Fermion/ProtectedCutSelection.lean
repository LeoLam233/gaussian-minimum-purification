import Gaussian.Physical.Fermion.SelectedSuffix
import Gaussian.Phase.ProtectedFrameSelection

set_option autoImplicit false
noncomputable section
open Module Gaussian.Phase
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem selected_prefix_range_eq_comap (k l : ℕ)
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k)) :
    (selectedCoefficientEmbedding k l R).toLinearMap.range =
      (prefixCoefficientEmbedding k l).toLinearMap.range.comap R.toLinearEquiv.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨y,?_⟩
    change prefixCoefficientEmbedding k l y=R (R.symm (prefixCoefficientEmbedding k l y))
    rw [R.apply_symm_apply]
  · rintro ⟨y,hy⟩
    refine ⟨y,?_⟩
    change R.symm (prefixCoefficientEmbedding k l y)=x
    change prefixCoefficientEmbedding k l y=R x at hy
    rw [hy,R.symm_apply_apply]

/-- An excess protected auxiliary coefficient space supplies an admissible
actual entropy-decreasing one-mode selection. The protected directions are fixed
pointwise, and exact equality forces the selected actual suffix state to be pure. -/
theorem exists_protected_entropy_selection (k : ℕ) (ρ : Density (1+k))
    (hρ : IsQuasifree ρ) (A : Submodule ℝ (CoefficientSpace (1+k)))
    (hA : finrank ℝ (CoefficientSpace (1+k)) < 2*finrank ℝ Aᗮ)
    (hterm : (suffixCoefficientEmbedding k 1).toLinearMap.range ≤ Aᗮ) :
    ∃ R : CoefficientSpace (1+k) ≃ₗᵢ[ℝ] CoefficientSpace (1+k),
      ∃ U : Matrix.unitaryGroup (Occupation (1+k)) ℂ,
      Implements (1+k) R U ∧ (∀ x ∈ A,R x=x) ∧
      Sᵥₙ (prefixRestriction k 1 (ρ.uConj U)) ≤ Sᵥₙ ρ ∧
      (Sᵥₙ (prefixRestriction k 1 (ρ.uConj U))=Sᵥₙ ρ →
        ∃ ψ,suffixRestriction k 1 (ρ.uConj U)=MState.pure ψ) := by
  have heven : Even (finrank ℝ (CoefficientSpace (1+k))) := by
    simp [CoefficientSpace,MajoranaIndex]
  obtain ⟨d⟩ := exists_skewAdaptation (covarianceGenerator ρ) (covarianceGenerator_skew ρ) heven
  obtain ⟨v,hv,hP,hD,hJ,hJc⟩ := d.complexStructure.exists_plane_of_excess Aᗮ hA
  let P := d.complexStructure.plane v
  let Q := (suffixCoefficientEmbedding k 1).toLinearMap.range
  let ix : MajoranaIndex 1 ≃ Fin 2 := (Fintype.equivFin _).trans (finCongr (by simp [MajoranaIndex]))
  let b := (EuclideanSpace.basisFun (MajoranaIndex 1) ℝ).reindex ix
  let t : Fin 2 → CoefficientSpace (1+k) := (suffixCoefficientEmbedding k 1) ∘ b
  have ht : Orthonormal ℝ t := b.orthonormal.comp_linearIsometry (suffixCoefficientEmbedding k 1)
  have htA (i : Fin 2) : t i ∈ Aᗮ := hterm ⟨b i,rfl⟩
  obtain ⟨R,hfix,hmap,hpair⟩ := exists_protected_paired_plane_selection d.complexStructure
    A P hJ hD hP t ht htA
  have htspan : Submodule.span ℝ (Set.range t)=Q := by
    rw [show Set.range t = (suffixCoefficientEmbedding k 1) '' Set.range b from Set.range_comp _ _]
    change Submodule.span ℝ ((suffixCoefficientEmbedding k 1).toLinearMap '' Set.range b.toBasis)=Q
    rw [← Submodule.map_span,b.toBasis.span_eq,Submodule.map_top]
  have hPQ : P.map R.toLinearEquiv.toLinearMap=Q := hmap.trans htspan
  have hpre : (prefixCoefficientEmbedding k 1).toLinearMap.range=Qᗮ := by
    dsimp [Q]
    rw [suffix_range_eq_prefix_orthogonal,Submodule.orthogonal_orthogonal]
  have hrange : (selectedCoefficientEmbedding k 1 R).toLinearMap.range=Pᗮ := by
    rw [selected_prefix_range_eq_comap,hpre]
    exact (d.complexStructure.transport_invariant_split R P Q hJ hPQ).2.2.2
  have hselected : d.complexStructure.IsInvariant
      (selectedCoefficientEmbedding k 1 R).toLinearMap.range := by
    rw [hrange]
    exact hJc
  obtain ⟨U,hU⟩ := orthogonal_implemented (1+k) R
  exact ⟨R,U,hU,hfix,selectedRestriction_entropy_le k 1 ρ hρ d R U hU hselected,
    selectedSuffix_pure_of_entropy_eq k 1 ρ hρ d R U hU hselected⟩

end Gaussian.Physical.Fermion
