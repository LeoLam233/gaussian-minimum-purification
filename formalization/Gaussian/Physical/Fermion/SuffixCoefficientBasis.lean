import Gaussian.Physical.Fermion.SuffixRestriction
import Gaussian.Physical.Fermion.StateAction

/-! The actual complete-mode partial trace acts by a genuine coefficient
isometric embedding, proved independently of all spectral entropy definitions. -/
set_option autoImplicit false
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def suffixMajoranaIndex (k l : ℕ) (a : MajoranaIndex l) : MajoranaIndex (l+k) :=
  (suffixIndex k l a.1,a.2)

theorem suffixMajoranaIndex_injective (k l : ℕ) : Function.Injective (suffixMajoranaIndex k l) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    have hi := congrArg (fun z : MajoranaIndex (l+k) => z.1.val) h
    simp only [suffixMajoranaIndex,suffixIndex_val] at hi
    omega
  · exact congrArg (fun z : MajoranaIndex (l+k) => z.2) h

def suffixCoefficientMap (k l : ℕ) : CoefficientSpace l →ₗ[ℝ] CoefficientSpace (l+k) :=
  (EuclideanSpace.basisFun (MajoranaIndex l) ℝ).toBasis.constr ℝ
    (fun a => coefficientBasis (l+k) (suffixMajoranaIndex k l a))

@[simp] theorem suffixCoefficientMap_basis (k l : ℕ) (a : MajoranaIndex l) :
    suffixCoefficientMap k l (coefficientBasis l a) = coefficientBasis (l+k) (suffixMajoranaIndex k l a) := by
  simpa only [suffixCoefficientMap, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, coefficientBasis] using
    (EuclideanSpace.basisFun (MajoranaIndex l) ℝ).toBasis.constr_basis ℝ
      (fun a => coefficientBasis (l+k) (suffixMajoranaIndex k l a)) a

def suffixCoefficientEmbedding (k l : ℕ) : CoefficientSpace l →ₗᵢ[ℝ] CoefficientSpace (l+k) := by
  let b := EuclideanSpace.basisFun (MajoranaIndex l) ℝ
  have h := (EuclideanSpace.basisFun (MajoranaIndex (l+k)) ℝ).orthonormal.comp
    (suffixMajoranaIndex k l) (suffixMajoranaIndex_injective k l)
  have hb : Orthonormal ℝ (fun a => coefficientBasis (l+k) (suffixMajoranaIndex k l a)) := by
    simpa only [Function.comp_def,EuclideanSpace.basisFun_apply] using h
  have he : (suffixCoefficientMap k l ∘ b.toBasis) =
      (fun a => coefficientBasis (l+k) (suffixMajoranaIndex k l a)) := by
    funext a
    simp only [Function.comp_apply,OrthonormalBasis.coe_toBasis,b,
      EuclideanSpace.basisFun_apply,suffixCoefficientMap_basis]
  have hf : Orthonormal ℝ (suffixCoefficientMap k l ∘ b.toBasis) := by
    rw [he]
    exact hb
  exact (suffixCoefficientMap k l).isometryOfOrthonormal (v := b.toBasis) b.orthonormal hf

@[simp] theorem suffixCoefficientEmbedding_basis (k l : ℕ) (a : MajoranaIndex l) :
    suffixCoefficientEmbedding k l (coefficientBasis l a) =
      coefficientBasis (l+k) (suffixMajoranaIndex k l a) := suffixCoefficientMap_basis k l a

end Gaussian.Physical.Fermion
