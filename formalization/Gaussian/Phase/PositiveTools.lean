import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith

/-! Exact positive-operator support lemmas. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy–Schwarz for the possibly degenerate quadratic form of a positive map. -/
theorem positive_cauchy_schwarz {K : E →ₗ[ℝ] E} (hK : K.IsPositive) (x y : E) :
    ⟪K x,y⟫ ^ 2 ≤ ⟪K x,x⟫ * ⟪K y,y⟫ := by
  have hcross : ⟪K y,x⟫ = ⟪K x,y⟫ := by
    rw [hK.isSymmetric, real_inner_comm]
  have hq : ∀ t : ℝ, 0 ≤ ⟪K y,y⟫ * (t*t) + (2*⟪K x,y⟫)*t + ⟪K x,x⟫ := by
    intro t
    have h := hK.inner_nonneg_left (x + t • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, hcross] at h
    nlinarith
  have h := discrim_le_zero hq
  dsimp [discrim] at h
  nlinarith

/-- Exact zero quadratic weight annihilates the vector; no spectral gap is needed. -/
theorem positive_inner_eq_zero_iff {K : E →ₗ[ℝ] E} (hK : K.IsPositive) (x : E) :
    ⟪K x,x⟫ = 0 ↔ K x = 0 := by
  constructor
  · intro hx
    have h := positive_cauchy_schwarz hK x (K x)
    rw [hx,zero_mul] at h
    have hh : ⟪K x,K x⟫ = 0 := by nlinarith [sq_nonneg ⟪K x,K x⟫]
    exact inner_self_eq_zero.mp hh
  · intro hx
    rw [hx,inner_zero_left]

/-- Positive and injective is positive definite, in any real inner-product space. -/
theorem positive_inner_pos_of_injective {K : E →ₗ[ℝ] E} (hK : K.IsPositive)
    (hKi : Function.Injective K) {x : E} (hx : x ≠ 0) : 0 < ⟪K x,x⟫ := by
  apply lt_of_le_of_ne (hK.inner_nonneg_left x)
  intro hzero
  have hKx := (positive_inner_eq_zero_iff hK x).mp hzero.symm
  exact hx (hKi (by simpa using hKx))

end Gaussian.Phase
