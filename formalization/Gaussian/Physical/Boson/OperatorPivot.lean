import Gaussian.Algebra.SymplecticPivot
import Gaussian.Physical.Boson.ConfigurationSymplectic

/-! A coordinate-free symmetric pivot for finite real configuration operators.
The matrix choice is transported through a proved orthonormal star-algebra equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Matrix Module
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Orthonormal coordinates preserve the actual operator product and adjoint. -/
def continuousEndCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) : (E →L[ℝ] E) ≃⋆ₐ[ℝ] Matrix ι ι ℝ :=
  ({ LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap } :
      (E →ₗ[ℝ] E) ≃⋆ₐ[ℝ] (E →L[ℝ] E)).symm.trans (LinearMap.toMatrixOrthonormal b)

lemma continuousEndCoordinates_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    continuousEndCoordinates b A = LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap := rfl

lemma continuousEndCoordinates_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (x : E) :
    continuousEndCoordinates b A *ᵥ b.toBasis.equivFun x = b.toBasis.equivFun (A x) := by
  rw [continuousEndCoordinates_apply]
  simpa only [Basis.equivFun_apply,ContinuousLinearMap.coe_coe] using A.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis x

/-- A common trivial kernel and the true adjoint compatibility produce an actual symmetric pivot. -/
theorem exists_selfAdjoint_operator_pivot (A C : E →L[ℝ] E)
    (hker : ∀ x : E, A x=0 → C x=0 → x=0)
    (hAC : star A*C=star C*A) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ IsUnit (A+S*C) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let Φ := continuousEndCoordinates b
  have hmat : (Φ A)ᵀ * Φ C = (Φ C)ᵀ * Φ A := by
    have h := congrArg Φ hAC
    simpa only [map_mul,map_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hker' : ∀ x : Fin (Module.finrank ℝ E) → ℝ, (Φ A) • x=0 → (Φ C) • x=0 → x=0 := by
    intro x hA hC
    simp only [Matrix.smul_eq_mulVec] at hA hC
    let y := b.toBasis.equivFun.symm x
    have hy (T : E →L[ℝ] E) (hT : Φ T *ᵥ x=0) : T y=0 := by
      apply b.toBasis.equivFun.injective
      rw [map_zero,← continuousEndCoordinates_mulVec]
      simpa only [y,b.toBasis.equivFun.apply_symm_apply] using hT
    have hz := hker y (hy A hA) (hy C hC)
    have h := congrArg b.toBasis.equivFun hz
    simpa only [y,b.toBasis.equivFun.apply_symm_apply,map_zero] using h
  obtain ⟨X,hX,hunit⟩ := Gaussian.Algebra.exists_symmetric_pivot_of_joint_kernel hker' hmat
  refine ⟨Φ.symm X,?_,?_⟩
  · change star (Φ.symm X)=Φ.symm X
    have hx : star X=X := by
      simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hX.eq
    have h := congrArg Φ.symm hx
    simpa only [map_star] using h
  · have h := hunit.map Φ.symm
    simpa only [map_add,map_mul,Φ.symm_apply_apply] using h

end Gaussian.Physical.Boson
