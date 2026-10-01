import Gaussian.Physical.Fermion.BlockIndices
import Gaussian.Physical.Fermion.StateAction

/-! The actual complete-mode partial trace acts by a genuine coefficient
isometric embedding, proved independently of all spectral entropy definitions. -/
set_option autoImplicit false
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def prefixMajoranaIndex (k l : ℕ) (a : MajoranaIndex k) : MajoranaIndex (l+k) :=
  (prefixIndex k l a.1,a.2)

theorem prefixMajoranaIndex_injective (k l : ℕ) : Function.Injective (prefixMajoranaIndex k l) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    have hi := congrArg (fun z : MajoranaIndex (l+k) => z.1.val) h
    simpa only [prefixMajoranaIndex,prefixIndex_val] using hi
  · exact congrArg (fun z : MajoranaIndex (l+k) => z.2) h

def prefixCoefficientMap (k l : ℕ) : CoefficientSpace k →ₗ[ℝ] CoefficientSpace (l+k) :=
  (EuclideanSpace.basisFun (MajoranaIndex k) ℝ).toBasis.constr ℝ
    (fun a => coefficientBasis (l+k) (prefixMajoranaIndex k l a))

@[simp] theorem prefixCoefficientMap_basis (k l : ℕ) (a : MajoranaIndex k) :
    prefixCoefficientMap k l (coefficientBasis k a) = coefficientBasis (l+k) (prefixMajoranaIndex k l a) := by
  simpa only [prefixCoefficientMap, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, coefficientBasis] using
    (EuclideanSpace.basisFun (MajoranaIndex k) ℝ).toBasis.constr_basis ℝ
      (fun a => coefficientBasis (l+k) (prefixMajoranaIndex k l a)) a

def prefixCoefficientEmbedding (k l : ℕ) : CoefficientSpace k →ₗᵢ[ℝ] CoefficientSpace (l+k) := by
  let b := EuclideanSpace.basisFun (MajoranaIndex k) ℝ
  have h := (EuclideanSpace.basisFun (MajoranaIndex (l+k)) ℝ).orthonormal.comp
    (prefixMajoranaIndex k l) (prefixMajoranaIndex_injective k l)
  have hb : Orthonormal ℝ (fun a => coefficientBasis (l+k) (prefixMajoranaIndex k l a)) := by
    simpa only [Function.comp_def,EuclideanSpace.basisFun_apply] using h
  have he : (prefixCoefficientMap k l ∘ b.toBasis) =
      (fun a => coefficientBasis (l+k) (prefixMajoranaIndex k l a)) := by
    funext a
    simp only [Function.comp_apply,OrthonormalBasis.coe_toBasis,b,
      EuclideanSpace.basisFun_apply,prefixCoefficientMap_basis]
  have hf : Orthonormal ℝ (prefixCoefficientMap k l ∘ b.toBasis) := by
    rw [he]
    exact hb
  exact (prefixCoefficientMap k l).isometryOfOrthonormal (v := b.toBasis) b.orthonormal hf

@[simp] theorem prefixCoefficientEmbedding_basis (k l : ℕ) (a : MajoranaIndex k) :
    prefixCoefficientEmbedding k l (coefficientBasis k a) =
      coefficientBasis (l+k) (prefixMajoranaIndex k l a) := prefixCoefficientMap_basis k l a

end Gaussian.Physical.Fermion
