import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A bounded linear image can be tested on an actual complete Hilbert basis. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Analysis
open scoped InnerProductSpace
variable {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inner_image_zero_of_basis (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] K) (u : K)
    (h : ∀ i, ⟪A (b i),u⟫_ℂ=0) : ∀ x, ⟪A x,u⟫_ℂ=0 := by
  have hz : A.adjoint u=0 := by
    apply b.repr.injective
    ext i
    simpa [HilbertBasis.repr_apply_apply,ContinuousLinearMap.adjoint_inner_right] using h i
  intro x
  rw [← ContinuousLinearMap.adjoint_inner_right,hz,inner_zero_right]

end Gaussian.Analysis
