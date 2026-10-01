import Gaussian.Physical.Fermion.PrefixCoefficientBasis
import Gaussian.Physical.Fermion.SuffixCoefficientBasis

set_option autoImplicit false
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem prefix_suffix_inner (k l : ℕ) (x : CoefficientSpace k) (y : CoefficientSpace l) :
    ⟪prefixCoefficientEmbedding k l x,suffixCoefficientEmbedding k l y⟫=0 := by
  let B : CoefficientSpace k →ₗ[ℝ] CoefficientSpace l →ₗ[ℝ] ℝ :=
    (innerₗ (CoefficientSpace (l+k))).compl₁₂
      (prefixCoefficientEmbedding k l).toLinearMap (suffixCoefficientEmbedding k l).toLinearMap
  have hB : B=0 := by
    apply (EuclideanSpace.basisFun (MajoranaIndex k) ℝ).toBasis.ext
    intro a
    apply (EuclideanSpace.basisFun (MajoranaIndex l) ℝ).toBasis.ext
    intro b
    have hne : prefixMajoranaIndex k l a ≠ suffixMajoranaIndex k l b := by
      intro h
      have hv := congrArg (fun z : MajoranaIndex (l+k) => z.1.val) h
      simp only [prefixMajoranaIndex,suffixMajoranaIndex,prefixIndex_val,suffixIndex_val] at hv
      have ha := a.1.isLt
      omega
    simp only [B,LinearMap.compl₁₂_apply,OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply,LinearIsometry.coe_toLinearMap,
      prefixCoefficientEmbedding_basis,suffixCoefficientEmbedding_basis]
    change ⟪coefficientBasis (l+k) (prefixMajoranaIndex k l a),
      coefficientBasis (l+k) (suffixMajoranaIndex k l b)⟫=0
    simp [coefficientBasis,EuclideanSpace.inner_single_left,hne]
  exact congrArg (fun C : CoefficientSpace k →ₗ[ℝ] CoefficientSpace l →ₗ[ℝ] ℝ => C x y) hB

/-- The two actual complete-mode coefficient embeddings are orthogonal
complements, including either empty block. -/
theorem suffix_range_eq_prefix_orthogonal (k l : ℕ) :
    (suffixCoefficientEmbedding k l).toLinearMap.range =
      (prefixCoefficientEmbedding k l).toLinearMap.rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro z ⟨y,rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro z ⟨x,rfl⟩
    exact prefix_suffix_inner k l x y
  · have hp : finrank ℝ (prefixCoefficientEmbedding k l).toLinearMap.range=2*k := by
      rw [LinearMap.finrank_range_of_inj (prefixCoefficientEmbedding k l).injective]
      simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
    have hs : finrank ℝ (suffixCoefficientEmbedding k l).toLinearMap.range=2*l := by
      rw [LinearMap.finrank_range_of_inj (suffixCoefficientEmbedding k l).injective]
      simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
    have he : finrank ℝ (CoefficientSpace (l+k))=2*(l+k) := by
      simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
    have ht := (prefixCoefficientEmbedding k l).toLinearMap.range.finrank_add_finrank_orthogonal
    omega

end Gaussian.Physical.Fermion
