import Gaussian.Physical.Fermion.ProtectedCutSelection
import Gaussian.Phase.InitialCoordinateSubspace

set_option autoImplicit false
noncomputable section
open Module Gaussian.Phase
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem initialModeSubspace_le_prefix_range (a k l : ℕ) (h : a≤l+k) (ha : a≤k) :
    initialModeSubspace a h ≤ (prefixCoefficientEmbedding k l).toLinearMap.range := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  refine ⟨coefficientBasis k (Fin.castLE ha i.1,i.2),?_⟩
  simp only [LinearIsometry.coe_toLinearMap]
  rw [prefixCoefficientEmbedding_basis]
  simp only [initialModeVectors,EuclideanSpace.basisFun_apply]
  congr 1
  apply Prod.ext
  · apply Fin.ext
    simp only [prefixMajoranaIndex,prefixIndex_val,Fin.val_castLE]
  · rfl

/-- The actual local selection theorem with every geometric existence premise
discharged by a strict excess of auxiliary over protected physical modes. -/
theorem exists_counted_entropy_selection (a k : ℕ) (hexcess : 2*a<1+k)
    (ρ : Density (1+k)) (hρ : IsQuasifree ρ) :
    ∃ R : CoefficientSpace (1+k) ≃ₗᵢ[ℝ] CoefficientSpace (1+k),
      ∃ U : Matrix.unitaryGroup (Occupation (1+k)) ℂ,
      Implements (1+k) R U ∧
      (∀ i : MajoranaIndex a,
        R (coefficientBasis (1+k) (Fin.castLE (by omega : a≤1+k) i.1,i.2)) =
          coefficientBasis (1+k) (Fin.castLE (by omega : a≤1+k) i.1,i.2)) ∧
      Sᵥₙ (prefixRestriction k 1 (ρ.uConj U)) ≤ Sᵥₙ ρ ∧
      (Sᵥₙ (prefixRestriction k 1 (ρ.uConj U))=Sᵥₙ ρ →
        ∃ ψ,suffixRestriction k 1 (ρ.uConj U)=MState.pure ψ) := by
  let h : a≤1+k := by omega
  let A : Submodule ℝ (CoefficientSpace (1+k)) := initialModeSubspace a h
  have hdim : finrank ℝ (CoefficientSpace (1+k)) < 2*finrank ℝ Aᗮ :=
    initialModeSubspace_orthogonal_excess a h hexcess
  have hterm : (suffixCoefficientEmbedding k 1).toLinearMap.range≤Aᗮ := by
    rw [suffix_range_eq_prefix_orthogonal]
    exact Submodule.orthogonal_le (initialModeSubspace_le_prefix_range a k 1 h (by omega))
  obtain ⟨R,U,hU,hfix,hle,heq⟩ := exists_protected_entropy_selection k ρ hρ A hdim hterm
  refine ⟨R,U,hU,?_,hle,heq⟩
  intro i
  apply hfix
  apply Submodule.subset_span
  refine ⟨i,?_⟩
  simp only [initialModeVectors,EuclideanSpace.basisFun_apply]

end Gaussian.Physical.Fermion
