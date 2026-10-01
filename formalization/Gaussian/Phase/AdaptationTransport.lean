import Gaussian.Phase.SkewAdaptation
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Transport a proved skew adaptation through an actual isometric covariance
intertwiner. The target operator is independently supplied. -/
def SkewAdaptationData.isometryTransport {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (e : F ≃ₗᵢ[ℝ] E) (S : F →ₗ[ℝ] F) (hS : ∀ x,e (S x)=T (e x)) :
    SkewAdaptationData S where
  J := e.symm.toLinearEquiv.conj d.J
  K := e.symm.toLinearEquiv.conj d.K
  square_neg x := by
    change e.symm (d.J (e (e.symm (d.J (e x))))) = -x
    rw [e.apply_symm_apply,d.square_neg,map_neg,e.symm_apply_apply]
  skew x y := by
    change ⟪e.symm (d.J (e x)),y⟫ = -⟪x,e.symm (d.J (e y))⟫
    rw [← e.inner_map_map (e.symm (d.J (e x))) y,
      ← e.inner_map_map x (e.symm (d.J (e y)))]
    simp only [e.apply_symm_apply]
    exact d.skew (e x) (e y)
  positive := (LinearMap.isPositive_linearIsometryEquiv_conj_iff e.symm).mpr d.positive
  factor x := by
    apply e.injective
    change e (S x) = e (e.symm (d.J (e (e.symm (d.K (e x))))))
    rw [e.apply_symm_apply,e.apply_symm_apply,hS,d.factor]
  commute x := by
    change e.symm (d.J (e (e.symm (d.K (e x))))) = e.symm (d.K (e (e.symm (d.J (e x)))))
    rw [e.apply_symm_apply,e.apply_symm_apply,d.commute]

theorem SkewAdaptationData.isometryTransport_eigenvalues
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (e : F ≃ₗᵢ[ℝ] E) (S : F →ₗ[ℝ] F) (hS : ∀ x,e (S x)=T (e x))
    {m : ℕ} (hE : finrank ℝ E=m) (hF : finrank ℝ F=m) :
    (d.isometryTransport e S hS).positive.isSymmetric.eigenvalues hF =
      d.positive.isSymmetric.eigenvalues hE := by
  apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff _ hF _ hE).mpr
  exact e.symm.toLinearEquiv.charpoly_conj d.K

end Gaussian.Phase
